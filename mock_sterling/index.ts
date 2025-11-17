import WebSocket from 'ws';
import * as pino from 'pino'
import type { MetaResponse, ProviderResponse } from './schemas.js';
import { clickResponseSchema, metaResponseSchema, providerResponseSchema } from './schemas.js';
import z from 'zod'
import { alloyXMLToDatum, xmlStringToJSON } from './alloyXML.js';

const DEFAULT_PORT = 4000;
const PING_DELAY_MS = 10000;

/**
 * Forge and Sterling only support one web-socket request at a time, and there
 * is no requestID field in messages sent. Thus, rather than using a promise map
 * to store multiple callbacks at once, this class uses a _single_ callback to
 * represent the active request, if any.
 */
export class MockWebSocketClient {
  logger: pino.Logger;
  private requestCounter: number;
  private ws: WebSocket | null;
  private connected: boolean;
  private port: number;
  private currentResponseResolver: ((data: any) => void) | null = null;

  constructor(port: number) {
    this.logger = pino.pino();
    this.requestCounter = 0;
    this.ws = null;
    this.connected = false;
    this.port = port;
  }

  disconnect() {
    if (this.ws) {
      this.ws.close();
    }
  }

  private sendPing() {
    this.logger.info('Sending ping...')
    this.send('ping')
  }

  connect() {
    return new Promise<void>((resolve, reject) => {
      this.ws = new WebSocket(`ws://localhost:${this.port}`);
    
      this.ws.on('open', () => {
        this.logger.info(`Successfully connected to server on port ${this.port}`);
        this.connected = true;
        setTimeout(() => this.sendPing(), PING_DELAY_MS);
        resolve();
      });

      this.ws.on('message', (data) => {
        const message = data.toString();
        if (message === 'pong') {
          this.logger.info('Received pong.')
          setTimeout(() => this.sendPing(), PING_DELAY_MS);
        } else {
          const response = this.handleServerMessage(message);
          if (this.currentResponseResolver) {
            this.currentResponseResolver(response);
            this.currentResponseResolver = null;
          } else {
            this.logger.warn('Received message but no resolver waiting');
          }
        }
      });

      this.ws.on('close', () => {
        this.logger.info('Disconnected from server');
        if (!this.connected) 
          reject(new Error('Connection closed before establishing'));
        this.connected = false;
      });

      this.ws.on('error', (error: Error) => {
        this.logger.error(`WebSocket error on port ${this.port}:`, error.message);
        reject(error);
      });
    });
  };

  isConnected = () => {
    return this.connected && this.ws && this.ws.readyState === WebSocket.OPEN;
  };

  private handleServerMessage(message: string): ProviderResponse {
    try {
      const data = JSON.parse(message);
      this.logger.info(`Received message from server: ${JSON.stringify(data)}`);
      return data
    } catch (error) {
      this.logger.error('Message was not valid JSON:', message);
      throw new Error('Invalid JSON')
    }
  };

  private send(message: string) {
    if (!this.connected) 
      throw new Error('Cannot send message: not connected to server');
    if(this.ws === null) 
      throw new Error('Cannot send message: web socket not created')
    this.ws.send(message);
    this.requestCounter++;
  };

  /** Send some request type. 
   * Give the type string flag and the schema for processing responses. 
   * Do not use this method for ping/pong */
  async sendRequest<T extends z.ZodType>(message: object, responseSchema: T): Promise<z.output<T>> {
    this.logger.info('Sending request');

    // Create promise for response
    const responsePromise = new Promise<z.output<T>>(resolve => {
      this.currentResponseResolver = resolve;
    });
    
    // Send the request
    this.send(JSON.stringify(message));
    
    // Wait for response
    // Note: To add a timeout, you could wrap this in a Promise.race() with a timeout promise:
    // return Promise.race([
    //   responsePromise,
    //   new Promise((_, reject) => setTimeout(() => reject(new Error('Timeout')), 30000))
    // ]);
    
    return responsePromise;
  };

  // async sendEvalRequest(id: unknown, code: unknown) {
  //   this.logger.info('Sending eval request');
  //   this.send({
  //     type: 'eval',
  //     payload: {
  //       id: id,
  //       code: code
  //     }
  //   });
  // };
}

async function main() {
  const args = process.argv.slice(2);
  const port = args[0] !== undefined ? parseInt(args[0], 10) : DEFAULT_PORT;
  
  if (isNaN(port)) {
    console.error(`Invalid port number provided: ${port}`);
    process.exit(1);
  }
  
  const mock = new MockWebSocketClient(port);
  process.on('SIGINT', () => {
    mock.logger.info('Disconnecting...');
    mock.disconnect();
    process.exit(0);
  });

  mock.logger.info(`Attempting to connect to WebSocket server on port ${port}...`);
  await mock.connect();

  // Get a list of run command keywords ("generator names") from Forge
  const metaResponse = await mock.sendRequest({type: "meta"}, metaResponseSchema)
  mock.logger.info(metaResponse.payload.generators)

  // Request structure to keep asking for new instances of the first generator name
  const clickFirst ={ 
    type: 'click', 
    payload: {
      onClick: 'next', 
      context: {generatorName: metaResponse.payload.generators[0]}
  }}

  // Get responses from the Mock Sterling
  const clickResponse1 = await mock.sendRequest(clickFirst, clickResponseSchema)

  if(clickResponse1.payload.enter[0] !== undefined) {
    const parsed1 = alloyXMLToDatum(clickResponse1.payload.enter[0].data)
    mock.logger.info(`${JSON.stringify(parsed1, null, 2)}`)
    
    // Disconnect from the mock after getting one datum; exit from the process gracefully
    mock.logger.info('Disconnecting...');
    mock.disconnect();
    process.exit(0);
  }
};

main()
export default MockWebSocketClient;

/* 
Notes moved to README.md
*/

