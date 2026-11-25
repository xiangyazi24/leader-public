import Leader.L4.Compiler.Code

/-!
# Literal native compiler dump

The reference emitter's instruction list, in its original order.
-/

namespace L4.Compiler.Native

/-- Dump nodes 0–63. -/
def literalChunkA : List Code := [
  .const .zero, -- 0
  .const .one, -- 1
  .const .p, -- 2
  .const .bm1, -- 3
  .const .max, -- 4
  .bconst false, -- 5
  .bconst true, -- 6
  .load 0 0, -- 7
  .load 0 1, -- 8
  .load 0 2, -- 9
  .load 0 3, -- 10
  .load 0 4, -- 11
  .load 0 5, -- 12
  .load 0 6, -- 13
  .load 0 7, -- 14
  .load 0 8, -- 15
  .header 0 0, -- 16
  .header 0 1, -- 17
  .header 0 2, -- 18
  .header 0 3, -- 19
  .header 0 4, -- 20
  .header 0 5, -- 21
  .header 0 6, -- 22
  .header 0 7, -- 23
  .header 0 8, -- 24
  .cmp 7 2, -- 25
  .cmpLt 25, -- 26
  .not 26, -- 27
  .and 16 27, -- 28
  .mux 28 0 7, -- 29
  .maskB 8, -- 30
  .maskB 9, -- 31
  .maskB 11, -- 32
  .maskB 12, -- 33
  .maskB 13, -- 34
  .maskB 15, -- 35
  .load 1 0, -- 36
  .load 1 1, -- 37
  .load 1 2, -- 38
  .load 1 3, -- 39
  .load 1 4, -- 40
  .load 1 5, -- 41
  .load 1 6, -- 42
  .load 1 7, -- 43
  .load 1 8, -- 44
  .header 1 0, -- 45
  .header 1 1, -- 46
  .header 1 2, -- 47
  .header 1 3, -- 48
  .header 1 4, -- 49
  .header 1 5, -- 50
  .header 1 6, -- 51
  .header 1 7, -- 52
  .header 1 8, -- 53
  .cmp 36 2, -- 54
  .cmpLt 54, -- 55
  .not 55, -- 56
  .and 45 56, -- 57
  .mux 57 0 36, -- 58
  .maskB 37, -- 59
  .maskB 38, -- 60
  .maskB 40, -- 61
  .maskB 41, -- 62
  .maskB 42 -- 63
]

/-- Dump nodes 64–127. -/
def literalChunkB : List Code := [
  .maskB 44, -- 64
  .load 2 0, -- 65
  .load 2 1, -- 66
  .load 2 2, -- 67
  .load 2 3, -- 68
  .load 2 4, -- 69
  .load 2 5, -- 70
  .load 2 6, -- 71
  .load 2 7, -- 72
  .load 2 8, -- 73
  .header 2 0, -- 74
  .header 2 1, -- 75
  .header 2 2, -- 76
  .header 2 3, -- 77
  .header 2 4, -- 78
  .header 2 5, -- 79
  .header 2 6, -- 80
  .header 2 7, -- 81
  .header 2 8, -- 82
  .cmp 65 2, -- 83
  .cmpLt 83, -- 84
  .not 84, -- 85
  .and 74 85, -- 86
  .mux 86 0 65, -- 87
  .maskB 66, -- 88
  .maskB 67, -- 89
  .maskB 69, -- 90
  .maskB 70, -- 91
  .maskB 71, -- 92
  .maskB 73, -- 93
  .add 58 1, -- 94
  .cmp 58 4, -- 95
  .cmpEq 95, -- 96
  .mux 96 2 94, -- 97
  .cmp 29 58, -- 98
  .cmpLt 98, -- 99
  .and 16 99, -- 100
  .not 100, -- 101
  .cmp 87 58, -- 102
  .cmpLt 102, -- 103
  .and 74 103, -- 104
  .not 104, -- 105
  .and 101 105, -- 106
  .cmp 58 29, -- 107
  .cmpLt 107, -- 108
  .cmp 94 29, -- 109
  .cmpLt 109, -- 110
  .and 108 110, -- 111
  .cmp 58 2, -- 112
  .cmpEq 112, -- 113
  .cmp 29 4, -- 114
  .cmpEq 114, -- 115
  .and 113 115, -- 116
  .not 116, -- 117
  .and 111 117, -- 118
  .cmp 58 87, -- 119
  .cmpLt 119, -- 120
  .cmp 94 87, -- 121
  .cmpLt 121, -- 122
  .and 120 122, -- 123
  .cmp 58 2, -- 124
  .cmpEq 124, -- 125
  .cmp 87 4, -- 126
  .cmpEq 126 -- 127
]

/-- Dump nodes 128–191. -/
def literalChunkC : List Code := [
  .and 125 127, -- 128
  .not 128, -- 129
  .and 123 129, -- 130
  .or 118 130, -- 131
  .bmux 45 106 131, -- 132
  .cmp 58 0, -- 133
  .cmpEq 133, -- 134
  .and 45 134, -- 135
  .not 135, -- 136
  .and 132 136, -- 137
  .add 29 1, -- 138
  .sub 2 1, -- 139
  .cmp 29 139, -- 140
  .cmpLt 140, -- 141
  .and 16 141, -- 142
  .cmp 138 58, -- 143
  .cmpLt 143, -- 144
  .and 142 144, -- 145
  .mux 145 138 58, -- 146
  .add 87 1, -- 147
  .sub 2 1, -- 148
  .cmp 87 148, -- 149
  .cmpLt 149, -- 150
  .and 74 150, -- 151
  .cmp 147 58, -- 152
  .cmpLt 152, -- 153
  .and 151 153, -- 154
  .mux 154 147 58, -- 155
  .cmp 146 155, -- 156
  .cmpLt 156, -- 157
  .mux 157 146 155, -- 158
  .cmp 158 58, -- 159
  .cmpLt 159, -- 160
  .add 29 1, -- 161
  .cmp 29 58, -- 162
  .cmpEq 162, -- 163
  .cmp 29 58, -- 164
  .cmpLt 164, -- 165
  .cmp 161 58, -- 166
  .cmpEq 166, -- 167
  .and 165 167, -- 168
  .or 163 168, -- 169
  .cmp 58 29, -- 170
  .cmpLt 170, -- 171
  .cmp 94 29, -- 172
  .cmpEq 172, -- 173
  .and 171 173, -- 174
  .or 169 174, -- 175
  .cmp 58 29, -- 176
  .cmpLt 176, -- 177
  .not 177, -- 178
  .not 16, -- 179
  .or 178 179, -- 180
  .and 175 180, -- 181
  .add 87 1, -- 182
  .cmp 87 58, -- 183
  .cmpEq 183, -- 184
  .cmp 87 58, -- 185
  .cmpLt 185, -- 186
  .cmp 182 58, -- 187
  .cmpEq 187, -- 188
  .and 186 188, -- 189
  .or 184 189, -- 190
  .cmp 58 87 -- 191
]

/-- Dump nodes 192–255. -/
def literalChunkD : List Code := [
  .cmpLt 191, -- 192
  .cmp 94 87, -- 193
  .cmpEq 193, -- 194
  .and 192 194, -- 195
  .or 190 195, -- 196
  .cmp 58 87, -- 197
  .cmpLt 197, -- 198
  .not 198, -- 199
  .not 74, -- 200
  .or 199 200, -- 201
  .and 196 201, -- 202
  .and 181 202, -- 203
  .and 45 203, -- 204
  .not 45, -- 205
  .cmp 29 58, -- 206
  .cmpEq 206, -- 207
  .cmp 29 97, -- 208
  .cmpEq 208, -- 209
  .or 207 209, -- 210
  .cmp 87 58, -- 211
  .cmpEq 211, -- 212
  .cmp 87 97, -- 213
  .cmpEq 213, -- 214
  .or 212 214, -- 215
  .and 210 215, -- 216
  .and 205 216, -- 217
  .bmux 217 5 45, -- 218
  .bmux 204 5 218, -- 219
  .bmux 160 6 219, -- 220
  .bmux 137 6 220, -- 221
  .mux 217 97 58, -- 222
  .mux 204 58 222, -- 223
  .mux 160 158 223, -- 224
  .mux 137 0 224, -- 225
  .scan5 58, -- 226
  .phaseEq 226 0, -- 227
  .phaseEq 226 1, -- 228
  .phaseEq 226 2, -- 229
  .phaseEq 226 3, -- 230
  .phaseEq 226 4, -- 231
  .phaseEq 226 5, -- 232
  .cmp 29 58, -- 233
  .cmpEq 233, -- 234
  .mux 234 33 30, -- 235
  .mux 234 34 31, -- 236
  .mux 234 14 10, -- 237
  .mux 234 35 32, -- 238
  .bmux 234 21 17, -- 239
  .bmux 234 22 18, -- 240
  .bmux 234 23 19, -- 241
  .bmux 234 24 20, -- 242
  .cmp 87 58, -- 243
  .cmpEq 243, -- 244
  .mux 244 91 88, -- 245
  .mux 244 92 89, -- 246
  .mux 244 72 68, -- 247
  .mux 244 93 90, -- 248
  .bmux 244 79 75, -- 249
  .bmux 244 80 76, -- 250
  .bmux 244 81 77, -- 251
  .bmux 244 82 78, -- 252
  .not 137, -- 253
  .not 160, -- 254
  .and 253 254 -- 255
]

/-- Dump nodes 256–319. -/
def literalChunkE : List Code := [
  .not 204, -- 256
  .and 255 256, -- 257
  .and 257 217, -- 258
  .and 258 228, -- 259
  .and 259 50, -- 260
  .cmp 43 0, -- 261
  .cmpEq 261, -- 262
  .and 260 262, -- 263
  .add 246 1, -- 264
  .cmp 3 264, -- 265
  .cmpLt 265, -- 266
  .mux 266 3 264, -- 267
  .mux 249 1 267, -- 268
  .shl3 63, -- 269
  .const .eight, -- 270
  .add 269 270, -- 271
  .cmp 43 0, -- 272
  .cmpEq 272, -- 273
  .sub 43 1, -- 274
  .cmp 271 274, -- 275
  .cmpLt 275, -- 276
  .mux 276 271 274, -- 277
  .mux 273 271 277, -- 278
  .mux 50 278 0, -- 279
  .bmux 273 5 51, -- 280
  .bmux 50 280 5, -- 281
  .sub 245 1, -- 282
  .mux 249 3 282, -- 283
  .add 235 1, -- 284
  .mux 50 0 284, -- 285
  .mux 52 283 285, -- 286
  .maskB 286, -- 287
  .cmp 235 62, -- 288
  .cmpLt 288, -- 289
  .not 289, -- 290
  .bmux 50 51 241, -- 291
  .cmp 238 64, -- 292
  .cmpLt 292, -- 293
  .or 50 293, -- 294
  .and 53 252, -- 295
  .mux 295 64 62, -- 296
  .mux 232 296 62, -- 297
  .mux 228 268 63, -- 298
  .mux 228 279 43, -- 299
  .mux 230 287 64, -- 300
  .bmux 227 290 50, -- 301
  .bmux 228 281 51, -- 302
  .bmux 229 291 52, -- 303
  .bmux 231 294 53, -- 304
  .mux 217 62 59, -- 305
  .mux 204 0 305, -- 306
  .mux 160 0 306, -- 307
  .mux 137 0 307, -- 308
  .mux 217 63 60, -- 309
  .mux 204 0 309, -- 310
  .mux 160 0 310, -- 311
  .mux 137 0 311, -- 312
  .mux 217 43 39, -- 313
  .mux 204 0 313, -- 314
  .mux 160 0 314, -- 315
  .mux 137 0 315, -- 316
  .mux 217 64 61, -- 317
  .mux 204 0 317, -- 318
  .mux 160 0 318 -- 319
]

/-- Dump nodes 320–383. -/
def literalChunkF : List Code := [
  .mux 137 0 319, -- 320
  .mux 217 297 62, -- 321
  .mux 204 0 321, -- 322
  .mux 160 0 322, -- 323
  .mux 137 0 323, -- 324
  .mux 217 298 63, -- 325
  .mux 204 0 325, -- 326
  .mux 160 0 326, -- 327
  .mux 137 0 327, -- 328
  .mux 217 299 43, -- 329
  .mux 204 0 329, -- 330
  .mux 160 0 330, -- 331
  .mux 137 0 331, -- 332
  .mux 217 300 64, -- 333
  .mux 204 0 333, -- 334
  .mux 160 0 334, -- 335
  .mux 137 0 335, -- 336
  .bmux 217 50 46, -- 337
  .bmux 204 5 337, -- 338
  .bmux 160 5 338, -- 339
  .bmux 137 5 339, -- 340
  .bmux 217 51 47, -- 341
  .bmux 204 5 341, -- 342
  .bmux 160 5 342, -- 343
  .bmux 137 5 343, -- 344
  .bmux 217 52 48, -- 345
  .bmux 204 5 345, -- 346
  .bmux 160 5 346, -- 347
  .bmux 137 5 347, -- 348
  .bmux 217 53 49, -- 349
  .bmux 204 5 349, -- 350
  .bmux 160 5 350, -- 351
  .bmux 137 5 351, -- 352
  .bmux 217 301 50, -- 353
  .bmux 204 5 353, -- 354
  .bmux 160 5 354, -- 355
  .bmux 137 5 355, -- 356
  .bmux 217 302 51, -- 357
  .bmux 204 5 357, -- 358
  .bmux 160 5 358, -- 359
  .bmux 137 5 359, -- 360
  .bmux 217 303 52, -- 361
  .bmux 204 5 361, -- 362
  .bmux 160 5 362, -- 363
  .bmux 137 5 363, -- 364
  .bmux 217 304 53, -- 365
  .bmux 204 5 365, -- 366
  .bmux 160 5 366, -- 367
  .bmux 137 5 367, -- 368
  .add 246 1, -- 369
  .cmp 3 369, -- 370
  .cmpLt 370, -- 371
  .mux 371 3 369, -- 372
  .mux 249 1 372, -- 373
  .shl3 63, -- 374
  .const .eight, -- 375
  .add 374 375, -- 376
  .cmp 43 0, -- 377
  .cmpEq 377, -- 378
  .sub 43 1, -- 379
  .cmp 376 379, -- 380
  .cmpLt 380, -- 381
  .mux 381 376 379, -- 382
  .mux 378 376 382 -- 383
]

/-- Dump nodes 384–447. -/
def literalChunkG : List Code := [
  .mux 50 383 0, -- 384
  .bmux 378 6 51, -- 385
  .bmux 50 385 5, -- 386
  .sub 245 1, -- 387
  .mux 249 3 387, -- 388
  .add 235 1, -- 389
  .mux 50 0 389, -- 390
  .mux 52 388 390, -- 391
  .maskB 391, -- 392
  .cmp 235 62, -- 393
  .cmpLt 393, -- 394
  .not 394, -- 395
  .bmux 50 51 241, -- 396
  .cmp 238 64, -- 397
  .cmpLt 397, -- 398
  .or 50 398, -- 399
  .and 53 252, -- 400
  .mux 400 64 62, -- 401
  .mux 232 401 62, -- 402
  .mux 228 373 63, -- 403
  .mux 228 384 43, -- 404
  .mux 230 392 64, -- 405
  .bmux 227 395 50, -- 406
  .bmux 228 386 51, -- 407
  .bmux 229 396 52, -- 408
  .bmux 231 399 53, -- 409
  .mux 217 62 59, -- 410
  .mux 204 0 410, -- 411
  .mux 160 0 411, -- 412
  .mux 137 0 412, -- 413
  .mux 217 63 60, -- 414
  .mux 204 0 414, -- 415
  .mux 160 0 415, -- 416
  .mux 137 0 416, -- 417
  .mux 217 43 39, -- 418
  .mux 204 0 418, -- 419
  .mux 160 0 419, -- 420
  .mux 137 0 420, -- 421
  .mux 217 64 61, -- 422
  .mux 204 0 422, -- 423
  .mux 160 0 423, -- 424
  .mux 137 0 424, -- 425
  .mux 217 402 62, -- 426
  .mux 204 0 426, -- 427
  .mux 160 0 427, -- 428
  .mux 137 0 428, -- 429
  .mux 217 403 63, -- 430
  .mux 204 0 430, -- 431
  .mux 160 0 431, -- 432
  .mux 137 0 432, -- 433
  .mux 217 404 43, -- 434
  .mux 204 0 434, -- 435
  .mux 160 0 435, -- 436
  .mux 137 0 436, -- 437
  .mux 217 405 64, -- 438
  .mux 204 0 438, -- 439
  .mux 160 0 439, -- 440
  .mux 137 0 440, -- 441
  .bmux 217 50 46, -- 442
  .bmux 204 5 442, -- 443
  .bmux 160 5 443, -- 444
  .bmux 137 5 444, -- 445
  .bmux 217 51 47, -- 446
  .bmux 204 5 446 -- 447
]

/-- Dump nodes 448–473. -/
def literalChunkH : List Code := [
  .bmux 160 5 447, -- 448
  .bmux 137 5 448, -- 449
  .bmux 217 52 48, -- 450
  .bmux 204 5 450, -- 451
  .bmux 160 5 451, -- 452
  .bmux 137 5 452, -- 453
  .bmux 217 53 49, -- 454
  .bmux 204 5 454, -- 455
  .bmux 160 5 455, -- 456
  .bmux 137 5 456, -- 457
  .bmux 217 406 50, -- 458
  .bmux 204 5 458, -- 459
  .bmux 160 5 459, -- 460
  .bmux 137 5 460, -- 461
  .bmux 217 407 51, -- 462
  .bmux 204 5 462, -- 463
  .bmux 160 5 463, -- 464
  .bmux 137 5 464, -- 465
  .bmux 217 408 52, -- 466
  .bmux 204 5 466, -- 467
  .bmux 160 5 467, -- 468
  .bmux 137 5 468, -- 469
  .bmux 217 409 53, -- 470
  .bmux 204 5 470, -- 471
  .bmux 160 5 471, -- 472
  .bmux 137 5 472 -- 473
]

/-- The exact neutral (radix-independent) opcode list. -/
def literal : List Code :=
  literalChunkA ++ literalChunkB ++ literalChunkC ++ literalChunkD ++ literalChunkE ++ literalChunkF ++ literalChunkG ++ literalChunkH

/-- Register holding the emitted NEED result. -/
def needIx : Nat := 263

/-- The nine word indices and nine header indices for each candidate. -/
def outIxLists : Bool → List Nat × List Nat
  | false => ([225, 308, 312, 316, 320, 324, 328, 332, 336], [221, 340, 344, 348, 352, 356, 360, 364, 368])
  | true => ([225, 413, 417, 421, 425, 429, 433, 437, 441], [221, 445, 449, 453, 457, 461, 465, 469, 473])

/-- Fixed-width form of the emitted output projections. -/
def outIx (delta : Bool) : (Fin 9 → Nat) × (Fin 9 → Nat) :=
  let p := outIxLists delta
  (fun i => p.1.getD i.val 0, fun i => p.2.getD i.val 0)

theorem literal_length : literal.length = 474 := by
  unfold literal
  simp only [List.length_append]
  decide

#print axioms literal_length
end L4.Compiler.Native
