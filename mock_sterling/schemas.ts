import z from 'zod'

export const metaResponseSchema = z.object({
    type: z.literal('meta'),
    version: z.number(),
    payload: z.object({
        evaluator: z.boolean(),
        generators: z.array(z.string()),
        name: z.string(),
        views: z.array(
                z.literal('graph')
            .or(z.literal('table')
            .or(z.literal('script'))))
    })
})

/** Expand this if we need to support more buttons */
export const onClickSchema = z.literal('next')
export const buttonSchema = z.object({
    text: z.string(), 
    onClick: onClickSchema})
export const dataUpdateSchema = z.object({
    id: z.number(),
    buttons: z.array(buttonSchema),
    evaluator: z.boolean()})
export const clickResponseSchema = z.object({
    type: z.literal('data'),
    version: z.number(),
    payload: z.object({
        enter: z.array(z.object({
            id: z.number(),
            format: z.literal('alloy').or(z.literal('forge')),
            data: z.string(), // alloy XML
            buttons: z.array(buttonSchema),
            evaluator: z.boolean()})),
        update: z.array(dataUpdateSchema),
        exit: z.array(z.string())
    })
})

export type ClickResponse = z.infer<typeof clickResponseSchema>
export type MetaResponse = z.infer<typeof metaResponseSchema>

export const providerResponseSchema = metaResponseSchema.or(clickResponseSchema)
export type ProviderResponse = z.infer<typeof providerResponseSchema>


/*

{
          "label": "seq/Int",
          "ID": "0",
          "parentID": "1",
          "builtin": "yes"
        },

        */

const sigSchema = z.object({
    label: z.string(),
    ID: z.coerce.number(),
    // Really I want a dependent type here: if ID is "univ" we're allowed undefined
    parentID: z.coerce.number().or(z.undefined()),
    builtin: z.literal('yes').or(z.undefined())
})
const fieldSchema = z.any()
export const alloyDatumSchema = z.object({
    alloy: z.object({
        instance: z.object({
            sig: z.array(sigSchema).or(sigSchema),
            field: z.array(fieldSchema).or(fieldSchema),
            bitwidth: z.coerce.number(),
            maxseq: z.coerce.number().optional(),
            command: z.string(), 
            filename: z.string(),
            version: z.string()
        }),
        source: z.undefined().or(z.object({
            filename: z.string(),
            content: z.string()
        })),
        builddate: z.string()
    })
})
export type AlloyDatum = z.infer<typeof alloyDatumSchema>
