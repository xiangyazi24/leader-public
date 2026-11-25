/-! Generated arithmetic part of the long K signature table.
Index zero is physical opcode 13, not SSA node zero. -/
namespace L4.BStarLongSignatures
inductive Kind where
  | unit | centerLoad | mux | bitCarry | shiftCarry | cmp | scan
  deriving DecidableEq, Repr
def arithmetic : List Kind :=
  [.unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .cmp, .unit, .unit, .mux, .unit, .unit, .unit, .unit, .unit, .unit,
   .centerLoad, .centerLoad, .centerLoad, .centerLoad, .centerLoad, .centerLoad, .centerLoad, .centerLoad, .centerLoad, .cmp, .unit, .unit,
   .mux, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .unit, .unit, .cmp, .unit, .unit, .mux, .unit, .unit, .unit, .unit,
   .unit, .unit, .bitCarry, .cmp, .mux, .cmp, .unit, .unit, .cmp, .unit, .unit, .unit,
   .cmp, .cmp, .unit, .cmp, .cmp, .unit, .unit, .unit, .cmp, .cmp, .unit, .cmp,
   .cmp, .unit, .unit, .unit, .unit, .unit, .cmp, .unit, .unit, .unit, .bitCarry, .bitCarry,
   .cmp, .unit, .cmp, .unit, .mux, .bitCarry, .bitCarry, .cmp, .unit, .cmp, .unit, .mux,
   .cmp, .mux, .cmp, .bitCarry, .cmp, .cmp, .cmp, .unit, .unit, .cmp, .cmp, .unit,
   .unit, .cmp, .unit, .unit, .unit, .unit, .bitCarry, .cmp, .cmp, .cmp, .unit, .unit,
   .cmp, .cmp, .unit, .unit, .cmp, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .cmp, .cmp, .unit, .cmp, .cmp, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .mux, .mux, .mux, .mux, .scan, .unit, .unit, .unit, .unit, .unit, .unit, .cmp,
   .mux, .mux, .mux, .mux, .unit, .unit, .unit, .unit, .cmp, .mux, .mux, .mux,
   .mux, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .cmp, .unit, .bitCarry, .cmp, .mux, .mux, .shiftCarry, .unit, .bitCarry, .cmp, .bitCarry,
   .cmp, .mux, .mux, .mux, .unit, .unit, .bitCarry, .mux, .bitCarry, .mux, .mux, .unit,
   .cmp, .unit, .unit, .cmp, .unit, .unit, .mux, .mux, .mux, .mux, .mux, .unit,
   .unit, .unit, .unit, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux,
   .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux,
   .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .unit,
   .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .unit, .unit, .unit, .unit, .unit, .bitCarry, .cmp, .mux, .mux, .shiftCarry,
   .unit, .bitCarry, .cmp, .bitCarry, .cmp, .mux, .mux, .mux, .unit, .unit, .bitCarry, .mux,
   .bitCarry, .mux, .mux, .unit, .cmp, .unit, .unit, .cmp, .unit, .unit, .mux, .mux,
   .mux, .mux, .mux, .unit, .unit, .unit, .unit, .mux, .mux, .mux, .mux, .mux,
   .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux,
   .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux, .mux,
   .mux, .mux, .mux, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit,
   .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit]
def muxInputs : List (Nat × Nat) :=
  [(30, 28), (49, 57), (68, 86), (77, 96), (113, 145), (120, 154), (122, 157), (169, 217), (170, 204), (171, 160),
   (172, 137), (181, 234), (182, 234), (183, 234), (184, 234), (190, 244), (191, 244), (192, 244), (193, 244), (210, 266),
   (211, 249), (218, 276), (219, 273), (220, 50), (224, 249), (226, 50), (227, 52), (235, 295), (236, 232), (237, 228),
   (238, 228), (239, 230), (244, 217), (245, 204), (246, 160), (247, 137), (248, 217), (249, 204), (250, 160), (251, 137),
   (252, 217), (253, 204), (254, 160), (255, 137), (256, 217), (257, 204), (258, 160), (259, 137), (260, 217), (261, 204),
   (262, 160), (263, 137), (264, 217), (265, 204), (266, 160), (267, 137), (268, 217), (269, 204), (270, 160), (271, 137),
   (272, 217), (273, 204), (274, 160), (275, 137), (310, 371), (311, 249), (318, 381), (319, 378), (320, 50), (324, 249),
   (326, 50), (327, 52), (335, 400), (336, 232), (337, 228), (338, 228), (339, 230), (344, 217), (345, 204), (346, 160),
   (347, 137), (348, 217), (349, 204), (350, 160), (351, 137), (352, 217), (353, 204), (354, 160), (355, 137), (356, 217),
   (357, 204), (358, 160), (359, 137), (360, 217), (361, 204), (362, 160), (363, 137), (364, 217), (365, 204), (366, 160),
   (367, 137), (368, 217), (369, 204), (370, 160), (371, 137), (372, 217), (373, 204), (374, 160), (375, 137)]
def tourNodes : List Nat :=
  [0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 25, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 54, 56, 57, 58, 59, 60, 61,
   62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 83, 85, 86, 87, 88, 89, 90, 91,
   92, 93, 94, 95, 97, 98, 100, 101, 102, 104, 105, 106, 107, 109, 111, 112, 114, 116, 117, 118,
   119, 121, 123, 124, 126, 128, 129, 130, 131, 132, 133, 135, 136, 137, 138, 139, 140, 142, 143, 145,
   146, 147, 148, 149, 151, 152, 154, 155, 156, 158, 159, 161, 162, 164, 166, 168, 169, 170, 172, 174,
   175, 176, 178, 179, 180, 181, 182, 183, 185, 187, 189, 190, 191, 193, 195, 196, 197, 199, 200, 201,
   202, 203, 204, 205, 206, 208, 210, 211, 213, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225,
   226, 227, 228, 229, 230, 231, 232, 233, 235, 236, 237, 238, 239, 240, 241, 242, 243, 245, 246, 247,
   248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 263, 264, 265, 267, 268, 269,
   270, 271, 272, 274, 275, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 290, 291, 292,
   294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313,
   314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333,
   334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353,
   354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 372, 373, 374,
   375, 376, 377, 379, 380, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 395, 396, 397,
   399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418,
   419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438,
   439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458,
   459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473]
def needIx : Nat := 263
def outDigits0 : List Nat := [225, 308, 312, 316, 320, 324, 328, 332, 336]
def outHeaders0 : List Nat := [221, 340, 344, 348, 352, 356, 360, 364, 368]
def outDigits1 : List Nat := [225, 413, 417, 421, 425, 429, 433, 437, 441]
def outHeaders1 : List Nat := [221, 445, 449, 453, 457, 461, 465, 469, 473]
end L4.BStarLongSignatures
