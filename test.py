from pprint import pprint

G = {0: None,
 1: 1,
 2: None,
 3: 3,
 4: None,
 5: None,
 6: 6,
 7: None,
 8: None,
 9: None,
 10: 10,
 11: 11,
 12: 12,
 13: None,
 14: None,
 15: None,
 16: 16,
 17: None,
 18: None,
 19: None,
 20: None,
 21: 21,
 22: 22,
 23: None,
 24: None,
 25: 25,
 26: 26,
 27: 27,
 28: 28,
 29: 29,
 30: None,
 31: None,
 32: None,
 33: 33,
 34: 34,
 35: None,
 36: 36,
 37: None,
 38: None,
 39: None,
 40: 40,
 41: 41,
 42: None,
 43: None,
 44: None,
 45: 45,
 46: 46,
 47: 47,
 48: None,
 49: None,
 50: None,
 51: 51,
 52: None,
 53: 53,
 54: None,
 55: 55,
 56: None,
 57: 57,
 58: 58,
 59: None,
 60: 60,
 61: None,
 62: None,
 63: 63,
 64: None,
 65: 65,
 66: 66,
 67: 67,
 68: 68,
 69: 69,
 70: None,
 71: None,
 72: None,
 73: None,
 74: 74,
 75: 75,
 76: None,
 77: None,
 78: 78,
 79: 79,
 80: None,
 81: None,
 82: None,
 83: 83,
 84: None,
 85: 85,
 86: None,
 87: None,
 88: None,
 89: 89,
 90: 90,
 91: 91,
 92: 92,
 93: 93,
 94: None,
 95: 95,
 96: 96,
 97: 97,
 98: 98,
 99: 99}

G = { k : v for k,v in G.items() if v is not None }

H = {1,
 4,
 8,
 10,
 12,
 14,
 22,
 23,
 24,
 26,
 34,
 35,
 40,
 46,
 52,
 53,
 54,
 56,
 62,
 66,
 67,
 69,
 73,
 74,
 77,
 86,
 98,
 99}

hp = 50

def shift(h):
    if h >= hp:
        if h-hp in H:
            return h-hp
        else:
            return h
    else:
        if h in H:
            return h+hp
        else:
            return h

Gshift = { h : shift(h) for h in range(100+hp) if shift(h) is not None}

#pprint(Gshift)

Gdiff = { h : v for h,v in Gshift.items() if (h,v) not in G.items() and not (h >= 100 and v is None)}
print("\n\nGdiff\n====================")
pprint(Gdiff)

def pre(h):
    txt = ", ".join([
              "h>=h'" if h >= hp else "h<h'",
              "h-h' ∈ H" if h-hp in H else "h-h' ∉ H",
              "h ∈ H" if h in H else "h ∉ H",
            ])
    vals = [ j for j in range(100+hp) if Gshift[j] == h]
    return (txt, vals)

preimg = { h : pre(h) for h in range(100) }
print("\n\npreimg\n====================")
pprint(preimg)

r = sorted(list(preimg.items()), key=lambda x: (len(x[1][1]), x[1][0]))
print("\n\npreimg sorted\n====================")
pprint(r)
