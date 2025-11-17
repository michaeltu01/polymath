import { XMLParser } from 'fast-xml-parser'
import { alloyDatumSchema, type AlloyDatum } from './schemas.js';

export function xmlStringToJSON(xml: string) {
    const parser = new XMLParser({
        ignoreAttributes: false,
        attributeNamePrefix: ""
    });
    return parser.parse(xml);
}

export function alloyXMLToDatum(xml: string): AlloyDatum | undefined {
    const json = xmlStringToJSON(xml)
    const parsed = alloyDatumSchema.safeParse(json)
    if(parsed.success) 
        return parsed.data
    console.error(parsed.error)
    return undefined
}