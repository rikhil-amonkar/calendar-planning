from z3 import *
import json

def main():
    cities = ["Mykonos", "Krakow", "Vilnius", "Helsinki", "Dubrovnik", "Oslo", "Madrid", "Paris"]
    durations = [4, 5, 2, 2, 3, 2, 5, 2]
    
    allowed_edges = set()
    allowed_edges.add((0,6)); allowed_edges.add((6,0))
    for v in [5, 3, 2, 7]:
        allowed_edges.add((1,v)); allowed_edges.add((v,1))
    for v in [5, 3, 7]:
        allowed_edges.add((2,v)); allowed_edges.add((v,2))
    for v in [4, 6]:
        allowed_edges.add((3,v)); allowed_edges.add((v,3))
    for v in [5, 6]:
        allowed_edges.add((4,v)); allowed_edges.add((v,4))
    allowed_edges.add((5,6)); allowed_edges.add((6,5))
    allowed_edges.add((6,7)); allowed_edges.add((7,6))
    allowed_edges.add((5,7)); allowed_edges.add((7,5))
    
    s = Solver()
    order = [Int(f'order_{i}') for i in range(8)]
    for i in range(8):
        s.add(order[i] >= 0, order[i] < 8)
    s.add(Distinct(order))
    
    starts = [Int(f'starts_{i}') for i in range(8)]
    s.add(starts[0] == 1)
    for i in range(1, 8):
        s.add(starts[i] == starts[i-1] + (durations[order[i-1]] - 1))
    
    for i in range(8):
        s.add(If(order[i] == 4, starts[i] == 2, True))
    for i in range(8):
        s.add(If(order[i] == 5, Or(starts[i] == 1, starts[i] == 2), True))
    for i in range(8):
        s.add(If(order[i] == 0, And(starts[i] >= 12, starts[i] <= 15), True))
    
    for i in range(7):
        conds = []
        for edge in allowed_edges:
            u, v = edge
            conds.append(And(order[i] == u, order[i+1] == v))
        s.add(Or(conds))
    
    if s.check() == sat:
        model = s.model()
        order_sol = [model.evaluate(order[i]).as_long() for i in range(8)]
        starts_sol = [model.evaluate(starts[i]).as_long() for i in range(8)]
        
        itinerary_list = []
        for i in range(8):
            city_index = order_sol[i]
            city_name = cities[city_index]
            start_day = starts_sol[i]
            end_day = start_day + durations[city_index] - 1
            for day in range(start_day, end_day + 1):
                itinerary_list.append({"day": day, "city": city_name})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()