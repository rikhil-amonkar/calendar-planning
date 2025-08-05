import json
from z3 import *

def main():
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    req_days = [4, 3, 2, 3, 5, 4]
    allowed_edges = [
        (2, 3),  # London and Copenhagen
        (3, 5),  # Copenhagen and Tallinn
        (5, 4),  # Tallinn and Oslo
        (0, 2),  # Mykonos and London
        (4, 1),  # Oslo and Nice
        (2, 1),  # London and Nice
        (0, 1),  # Mykonos and Nice
        (2, 4),  # London and Oslo
        (3, 1),  # Copenhagen and Nice
        (3, 4)   # Copenhagen and Oslo
    ]
    
    s = [Int(f's_{i}') for i in range(17)]
    solver = Solver()
    
    for i in range(17):
        solver.add(s[i] >= 0, s[i] < 6)
    
    for i in range(16):
        same_city = (s[i] == s[i+1])
        flight_ok = Or([Or(And(s[i] == a, s[i+1] == b), And(s[i] == b, s[i+1] == a)) for (a, b) in allowed_edges])
        solver.add(Or(same_city, flight_ok))
    
    for c in range(6):
        total = 0
        for i in range(16):
            total += If(Or(s[i] == c, s[i+1] == c), 1, 0)
        solver.add(total == req_days[c])
    
    solver.add(s[13] == 1)  # Start of day14 is Nice
    solver.add(s[14] == 1)  # End of day14 is Nice -> full day in Nice on day14
    solver.add(s[15] == 1)  # Start of day16 is Nice
    solver.add(s[16] == 1)  # End of day16 is Nice -> full day in Nice on day16
    
    oslo_full_days = []
    for day in range(10, 15):
        oslo_full_days.append(And(s[day-1] == 4, s[day] == 4))
    solver.add(Or(oslo_full_days))
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(17)]
        
        itinerary = []
        i = 0
        while i < 16:
            start_city = s_val[i]
            end_city = s_val[i+1]
            if start_city == end_city:
                start_day = i+1
                j = i
                while j < 15 and s_val[j+1] == s_val[j+2] and s_val[j+1] == start_city:
                    j += 1
                end_day = j+1
                if start_day == end_day:
                    day_range_str = f"Day {start_day}"
                else:
                    day_range_str = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range_str, "place": cities[start_city]})
                i = j + 1
            else:
                day_range_str = f"Day {i+1}"
                place_str = f"{cities[start_city]} and {cities[end_city]}"
                itinerary.append({"day_range": day_range_str, "place": place_str})
                i += 1
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()