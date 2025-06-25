from z3 import *
import json

def main():
    # Define the city indices and names
    cities = {
        0: "Reykjavik",
        1: "Riga",
        2: "Warsaw",
        3: "Istanbul",
        4: "Krakow"
    }
    
    # Given direct flights (undirected edges)
    given_edges = [(3,4), (2,0), (3,2), (1,3), (4,2), (1,2)]
    allowed_pairs = set()
    for u, v in given_edges:
        allowed_pairs.add((u, v))
        allowed_pairs.add((v, u))
    allowed_pairs = list(allowed_pairs)
    
    # Z3 solver setup
    s = [Int(f's{i}') for i in range(5)]
    solver = Solver()
    
    # Each s[i] is between 0 and 4
    for i in range(5):
        solver.add(And(s[i] >= 0, s[i] <= 4))
    
    # All cities are distinct
    solver.add(Distinct(s))
    
    # Function to get the length of stay for a city
    def z3_length(city):
        return If(city == 0, 7,
               If(city == 1, 2,
               If(city == 2, 3,
               If(city == 3, 6, 7))))
    
    # Arrays for start and end days
    start_day = [Int(f'start_{i}') for i in range(5)]
    end_day = [Int(f'end_{i}') for i in range(5)]
    
    # Constraints for start_day and end_day
    solver.add(start_day[0] == 1)
    solver.add(end_day[0] == start_day[0] + z3_length(s[0]) - 1)
    
    for i in range(1, 5):
        solver.add(start_day[i] == end_day[i-1])
        solver.add(end_day[i] == start_day[i] + z3_length(s[i]) - 1)
    
    # The entire trip must end at day 21
    solver.add(end_day[4] == 21)
    
    # Constraints for Riga and Istanbul
    for i in range(5):
        # Riga (city 1) must start on or before day 2
        solver.add(If(s[i] == 1, start_day[i] <= 2, True))
        # Istanbul (city 3) must start on or before day 7
        solver.add(If(s[i] == 3, start_day[i] <= 7, True))
    
    # Constraints for direct flights between consecutive cities
    for i in range(4):
        constraints = []
        for u, v in allowed_pairs:
            constraints.append(And(s[i] == u, s[i+1] == v))
        solver.add(Or(constraints))
    
    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        city_order = [model.eval(s[i]).as_long() for i in range(5)]
        start_days = [model.eval(start_day[i]).as_long() for i in range(5)]
        end_days = [model.eval(end_day[i]).as_long() for i in range(5)]
        
        itinerary = []
        for i in range(5):
            city_idx = city_order[i]
            city_name = cities[city_idx]
            s_day = start_days[i]
            e_day = end_days[i]
            itinerary.append({
                "day_range": f"Day {s_day}-{e_day}",
                "place": city_name
            })
            if i < 4:
                itinerary.append({
                    "day_range": f"Day {e_day}",
                    "place": city_name
                })
                next_city_idx = city_order[i+1]
                next_city_name = cities[next_city_idx]
                itinerary.append({
                    "day_range": f"Day {e_day}",
                    "place": next_city_name
                })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()