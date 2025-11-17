#!/bin/bash
# This script exists so that we can pass a provider port via `npm run run <port>`.
npx tsx index.ts "$@" | npx pino-pretty --translateTime SYS:hh:MM:ss:l --ignore hostname,pid