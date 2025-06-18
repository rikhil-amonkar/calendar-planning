from z3 import *
import json

def main():
    # Define city indices
    ams, vie, san, lyo = 0, 1, 2, 3
    reqs = {ams: 3, vie: 7, san: 4, lyo: 3}
    names = {ams: "Amsterdam", vie: "Vienna", san: "Santorini", lyo: "Lyon"}
    
    s = Solver()
    
    # Order of cities (4 integers)
    order = [Int('order_%d' % i) for i in range(4)]
    
    # Constraints: each city in [0,3] and distinct
    for i in range(4):
        s.add(order[i] >= 0, order[i] <= 3)
    s.add(Distinct(order[0], order[1], order[2], order[3]))
    
    # Departure days
    d0 = Int('d0')
    d1 = Int('d1')
    d2 = Int('d2')
    
    # d0 = required days of the first city
    s.add(d0 == If(order[0] == ams, reqs[ams],
                If(order[0] == vie, reqs[vie],
                If(order[0] == san, reqs[san], reqs[lyo]))))
    
    # d1 = d0 + reqs[order[1]] - 1
    s.add(d1 == d0 + 
          If(order[1] == ams, reqs[ams],
          If(order[1] == vie, reqs[vie],
          If(order[1] == san, reqs[san], reqs[lyo]))) - 1)
    
    # d2 = d1 + reqs[order[2]] - 1
    s.add(d2 == d1 + 
          If(order[2] == ams, reqs[ams],
          If(order[2] == vie, reqs[vie],
          If(order[2] == san, reqs[san], reqs[lyo]))) - 1)
    
    # Constraint: d2 = 15 - reqs[order[3]]
    s.add(d2 == 15 - 
          If(order[3] == ams, reqs[ams],
          If(order[3] == vie, reqs[vie],
          If(order[3] == san, reqs[san], reqs[lyo]))))
    
    # Event constraints for Amsterdam
    for i in range(4):
        cond_ams = (order[i] == ams)
        if i == 0:
            s.add(Implies(cond_ams, d0 >= 9))
        elif i == 1:
            s.add(Implies(cond_ams, And(d0 <= 11, d1 >= 9)))
        elif i == 2:
            s.add(Implies(cond_ams, And(d1 <= 11, d2 >= 9)))
        else:  # i == 3
            s.add(Implies(cond_ams, d2 <= 11))
    
    # Event constraints for Lyon
    for i in range(4):
        cond_lyo = (order[i] == lyo)
        if i == 0:
            s.add(Implies(cond_lyo, d0 >= 7))
        elif i == 1:
            s.add(Implies(cond_lyo, And(d0 <= 9, d1 >= 7)))
        elif i == 2:
            s.add(Implies(cond_lyo, And(d1 <= 9, d2 >= 7)))
        else:  # i == 3
            s.add(Implies(cond_lyo, d2 <= 9))
    
    # Flight connections
    for k in range(3):
        a = order[k]
        b = order[k+1]
        s.add(Or(
            And(a == ams, Or(b == vie, b == san, b == lyo)),
            And(a == vie, Or(b == ams, b == san, b == lyo)),
            And(a == san, Or(b == ams, b == vie)),
            And(a == lyo, Or(b == ams, b == vie))
        ))
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        ord_val = [m.evaluate(order[i]).as_long() for i in range(4)]
        d0_val = m.evaluate(d0).as_long()
        d1_val = m.evaluate(d1).as_long()
        d2_val = m.evaluate(d2).as_long()
        
        # Build itinerary
        itinerary = []
        city0 = ord_val[0]
        itinerary.append({"day_range": "Day 1-{}".format(d0_val), "place": names[city0]})
        itinerary.append({"day_range": "Day {}".format(d0_val), "place": names[city0]})
        city1 = ord_val[1]
        itinerary.append({"day_range": "Day {}".format(d0_val), "place": names[city1]})
        itinerary.append({"day_range": "Day {}-{}".format(d0_val, d1_val), "place": names[city1]})
        itinerary.append({"day_range": "Day {}".format(d1_val), "place": names[city1]})
        city2 = ord_val[2]
        itinerary.append({"day_range": "Day {}".format(d1_val), "place": names[city2]})
        itinerary.append({"day_range": "Day {}-{}".format(d1_val, d2_val), "place": names[city2]})
        itinerary.append({"day_range": "Day {}".format(d2_val), "place": names[city2]})
        city3 = ord_val[3]
        itinerary.append({"day_range": "Day {}".format(d2_val), "place": names[city3]})
        itinerary.append({"day_range": "Day {}-14".format(d2_val), "place": names[city3]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()