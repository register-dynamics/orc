var skeleton = require('../skeleton');
var Fraction = require('fraction.js');
var assert = require('assert');
var inspect = require('util').inspect;

VECTORS = [
 [ "<^FEFF\t",          new Fraction(-257)],
 [ "<_00\t",            new Fraction(-256)],
 [ "<_01\t",            new Fraction(-255)],
 [ "<_FE\t",            new Fraction(-2)],
 [ "<_FF\t",            new Fraction(-1)],
 [ "<_FF^FEFF~",        new Fraction(0).sub(256, 257)],
 [ "<_FF_00~",          new Fraction(0).sub(255, 256)],
 [ "<_FF_01~",          new Fraction(0).sub(254, 255)],
 [ "<_FF_FC~",          new Fraction(0).sub(3, 4)],
 [ "<_FF_FD~",          new Fraction(0).sub(2, 3)],
 [ "<_FF_FE!02\t",      new Fraction(0).sub(3, 5)],
 [ "<_FF_FE!03\t",      new Fraction(0).sub(4, 7)],
 [ "<_FF_FE~",          new Fraction(0).sub(1, 2)],
 [ "<_FF_FF!03\t",      new Fraction(0).sub(1, 4)],
 [ "<_FF_FF!04\t",      new Fraction(0).sub(1, 5)],
 [ "<_FF_FF!04_FA~",    new Fraction(0).sub(6, 31)],
 [ "<_FF_FF!04_FB~",    new Fraction(0).sub(5, 26)],
 [ "<_FF_FF!04_FC~",    new Fraction(0).sub(4, 21)],
 [ "<_FF_FF!05\t",      new Fraction(0).sub(1, 6)],
 [ "<_FF_FF!FF\t",      new Fraction(0).sub(1, 256)],
 [ "<_FF_FF\"0100\t",   new Fraction(0).sub(1, 257)],
 [ "> \t",              new Fraction(0)],
 [ "> _FD~",            new Fraction(0).add(1/3)],
 [ "> _FE~",            new Fraction(0).add(1/2)],
 [ "> _FF!03\t",        new Fraction(0).add(3/4)],
 [ "> _FF!04\t",        new Fraction(0).add(4/5)],
 [ ">!01\t",            new Fraction(1)],
 [ ">!01^FEFE~",        new Fraction(1).add(1, 258)],
 [ ">!01^FEFF\"0101\t", new Fraction(1).add(257, 66050)],
 [ ">!01^FEFF~",        new Fraction(1).add(1, 257)],
 [ ">!01_00~",          new Fraction(1).add(1, 256)],
 [ ">!01_01~",          new Fraction(1).add(1, 255)],
 [ ">!01_02~",          new Fraction(1).add(1, 254)],
 [ ">!01_12~",          new Fraction(1).add(1, 238)],
 [ ">!01_E2~",          new Fraction(1).add(1, 30)],
 [ ">!01_EA~",          new Fraction(1).add(1, 22)],
 [ ">!01_EB~",          new Fraction(1).add(1, 21)],
 [ ">!01_EC!02\t",      new Fraction(1).add(2, 41)],
 [ ">!01_EC!FF\t",      new Fraction(1).add(255, 5101)],
 [ ">!01_EC\"0100\t",   new Fraction(1).add(256, 5121)],
 [ ">!01_EC~",          new Fraction(1).add(1, 20)],
 [ ">!01_FD!02\t",      new Fraction(1).add(2, 7)],
 [ ">!01_FD!02^FEFF~",  new Fraction(1).add(515, 1802)],
 [ ">!01_FD!02_00~",    new Fraction(1).add(513, 1795)],
 [ ">!01_FD!02_FE~",    new Fraction(1).add(5, 17)],
 [ ">!01_FD!03\t",      new Fraction(1).add(3, 10)],
 [ ">!01_FD!FF\t",      new Fraction(1).add(255, 766)],
 [ ">!01_FD\"0100\t",   new Fraction(1).add(256, 769)],
 [ ">!01_FD~",          new Fraction(1).add(1, 3)],
 [ ">!01_FE~",          new Fraction(1).add(1, 2)],
]

INVALID = [
 [ ">!01_EC \t",        null], // Invalid encoding - last fraction can't be 1/0.
 [ ">!01_EC _F6~",      null], // Invalid encoding - non-first fraction can't be 0.
 [ ">!01_EC!00\t",      null], // Invalid encoding - last fraction can't be 1/0;
 [ ">!01_EC!01\t",      new Fraction(1).add(1, 21)], // Non canonical encoding - last fraction can't be 1/1.
 [ ">!01_FD!02_FF~",    new Fraction(1).add(3, 10)], // Non canonical encoding - last fraction can't be 1/1.
 [ "<_FF_FE!01\t",      new Fraction(0).sub(2, 3)], // Invalid encoding - last fraction can't be 1/1.
]

describe("Decoding numbers", () => {
  VECTORS.forEach(vector => {
    var input = vector[0];
    var expected = vector[1];
    it("correctly decodes " + inspect(input), () => {
      var result = skeleton.parseOne(input);
      assert(expected.equals(result), "Got " + inspect(result) + ", expected " + inspect(expected));
    })
  })

  INVALID.forEach(vector => {
    var input = vector[0];
    it("rejects " + inspect(input), () => {
      assert.throws(() => skeleton.parseOne(input));
    })
  })
})
