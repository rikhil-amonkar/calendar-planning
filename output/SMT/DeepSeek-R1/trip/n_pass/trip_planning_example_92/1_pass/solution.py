import z3
import json

def main():
    s_D, s_R, s_V = z3.Ints('s_D s_R s_V')
    e_D, e_R, e_V = z3.Ints('e_D e_R e_V')
    starts = [s_D, s_R, s_V]
    ends = [e_D, e_R, e_V]
    
    o0, o1, o2 = z3.Ints('o0 o1 o2')
    order = [o0, o1, o2]
    
    cities = ["Dublin", "Riga", "Vilnius"]
    
    solver = z3.Solver()
    
    # Durations
    solver.add(e_D - s_D + 1 == 2)
    solver.add(e_R - s_R + 1 == 5)
    solver.add(e_V - s_V + 1 == 7)
    
    # Bounds and ordering
    for s in starts:
        solver.add(s >= 1, s <= 12)
    for e in ends:
        solver.add(e >= 1, e <= 12)
    for i in range(3):
        solver.add(starts[i] <= ends[i])
    
    # Order: distinct and in [0,2]
    solver.add(z3.Distinct(order))
    for o in order:
        solver.add(o >= 0, o <= 2)
    
    # First city starts at 1, last ends at 12
    solver.add(starts[order[0]] == 1)
    solver.add(ends[order[2]] == 12)
    
    # Connections: end of one = start of next
    solver.add(ends[order[0]] == starts[order[1]])
    solver.add(ends[order[1]] == starts[order[2]])
    
    # Flight connections: consecutive cities must be adjacent
    solver.add(z3.Or(
        z3.And(order[0] == 0, order[1] == 1),
        z3.And(order[0] == 1, order[1] == 0),
        z3.And(order[0] == 1, order[1] == 2),
        z3.And(order[0] == 2, order[1] == 1)
    ))
    solver.add(z3.Or(
        z3.And(order[1] == 0, order[2] == 1),
        z3.And(order[1] == 1, order[2] == 0),
        z3.And(order[1] == 1, order[2] == 2),
        z3.And(order[1] == 2, order[2] == 1)
    ))
    
    if solver.check() == z3.sat:
        m = solver.model()
        o0_val = m[o0].as_long()
        o1_val = m[o1].as_long()
        o2_val = m[o2].as_long()
        order_vals = [o0_val, o1_val, o2_val]
        
        s_vals = [m.eval(s_D).as_long(), m.eval(s_R).as_long(), m.eval(s_V).as_long()]
        e_vals = [m.eval(e_D).as_long(), m.eval(e_R).as_long(), m.eval(e_V).as_long()]
        
        flight_day1 = e_vals[order_vals[0]]
        flight_day2 = e_vals[order_vals[1]]
        
        itinerary = []
        city0 = cities[order_vals[0]]
        itinerary.append({"day_range": f"Day {s_vals[order_vals[0]]}-{e_vals[order_vals[0]]}", "place": city0})
        itinerary.append({"day_range": f"Day {flight_day1}", "place": city0})
        city1 = cities[order_vals[1]]
        itinerary.append({"day_range": f"Day {flight_day1}", "place": city1})
        itinerary.append({"day_range": f"Day {s_vals[order_vals[1]]}-{e_vals[order_vals[1]]}", "place": city1})
        itinerary.append({"day_range": f"Day {flight_day2}", "place": city1})
        city2 = cities[order_vals[2]]
        itinerary.append({"day_range": f"Day {flight_day2}", "place": city2})
        itinerary.append({"day_range": f"Day {s_vals[order_vals[2]]}-{e_vals[order_vals[2]]}", "place": city2})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()