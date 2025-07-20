from z3 import *

def main():
    cities = ["Amsterdam", "Edinburgh", "Brussels", "Vienna", "Berlin", "Reykjavik"]
    req_array = [4, 5, 5, 5, 4, 5]
    flight_pairs = [
        (0, 1), (0, 3), (0, 4), (0, 5),
        (1, 2), (1, 4),
        (2, 3), (2, 4), (2, 5),
        (3, 4), (3, 5),
        (4, 5)
    ]
    
    s = Solver()
    order = [Int(f"order_{i}") for i in range(6)]
    
    for i in range(6):
        s.add(And(order[i] >= 0, order[i] < 6))
    s.add(Distinct(order))
    
    s0 = 1
    e0 = s0 + req_array[order[0]] - 1
    s1 = e0
    e1 = s1 + req_array[order[1]] - 1
    s2 = e1
    e2 = s2 + req_array[order[2]] - 1
    s3 = e2
    e3 = s3 + req_array[order[3]] - 1
    s4 = e3
    e4 = s4 + req_array[order[4]] - 1
    s5 = e4
    e5 = s5 + req_array[order[5]] - 1
    
    s.add(e5 == 23)
    
    def has_flight(a, b):
        conditions = []
        for (x, y) in flight_pairs:
            conditions.append(Or(And(a == x, b == y), And(a == y, b == x)))
        return Or(conditions)
    
    for i in range(5):
        s.add(has_flight(order[i], order[i+1]))
    
    ams_constraint = Or(
        And(order[0] == 0, s0 <= 5, e0 >= 8),
        And(order[1] == 0, s1 <= 5, e1 >= 8),
        And(order[2] == 0, s2 <= 5, e2 >= 8),
        And(order[3] == 0, s3 <= 5, e3 >= 8),
        And(order[4] == 0, s4 <= 5, e4 >= 8),
        And(order[5] == 0, s5 <= 5, e5 >= 8)
    )
    s.add(ams_constraint)
    
    ber_constraint = Or(
        And(order[0] == 4, s0 <= 16, e0 >= 19),
        And(order[1] == 4, s1 <= 16, e1 >= 19),
        And(order[2] == 4, s2 <= 16, e2 >= 19),
        And(order[3] == 4, s3 <= 16, e3 >= 19),
        And(order[4] == 4, s4 <= 16, e4 >= 19),
        And(order[5] == 4, s5 <= 16, e5 >= 19)
    )
    s.add(ber_constraint)
    
    rey_constraint = Or(
        And(order[0] == 5, s0 <= 12, e0 >= 16),
        And(order[1] == 5, s1 <= 12, e1 >= 16),
        And(order[2] == 5, s2 <= 12, e2 >= 16),
        And(order[3] == 5, s3 <= 12, e3 >= 16),
        And(order[4] == 5, s4 <= 12, e4 >= 16),
        And(order[5] == 5, s5 <= 12, e5 >= 16)
    )
    s.add(rey_constraint)
    
    if s.check() == sat:
        model = s.model()
        order_vals = [model.evaluate(order[i]).as_long() for i in range(6)]
        city_names = [cities[idx] for idx in order_vals]
        
        s_vals = [1]
        e_vals = [s_vals[0] + req_array[order_vals[0]] - 1]
        for i in range(1, 6):
            s_vals.append(e_vals[i-1])
            e_vals.append(s_vals[i] + req_array[order_vals[i]] - 1)
        
        itinerary_list = []
        for i in range(6):
            start = s_vals[i]
            end = e_vals[i]
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": city_names[i]})
            if i < 5:
                itinerary_list.append({"day_range": f"Day {end}", "place": city_names[i]})
                itinerary_list.append({"day_range": f"Day {end}", "place": city_names[i+1]})
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()