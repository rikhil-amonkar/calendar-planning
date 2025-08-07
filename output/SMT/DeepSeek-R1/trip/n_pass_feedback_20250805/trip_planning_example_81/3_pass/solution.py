from z3 import *
import json

def main():
    s = Solver()
    
    num_days = 9
    cities = ["Mykonos", "Budapest", "Hamburg"]
    cidx = {name: idx for idx, name in enumerate(cities)}
    
    # Variables: in_city[day][city] for day 1 to 9
    in_city = [[Bool(f"day{day}_{city}") for city in cities] for day in range(1, num_days+1)]
    
    # Fixed constraints: Must be in Mykonos on day 4 and day 9
    s.add(in_city[3][cidx["Mykonos"]] == True)  # day4 (index 3 in 0-indexed list for days 1-9)
    s.add(in_city[8][cidx["Mykonos"]] == True)  # day9 (index 8)
    
    # Total days constraints
    total_mykonos = 0
    total_budapest = 0
    total_hamburg = 0
    for day_idx in range(num_days):
        total_mykonos += If(in_city[day_idx][cidx["Mykonos"]], 1, 0)
        total_budapest += If(in_city[day_idx][cidx["Budapest"]], 1, 0)
        total_hamburg += If(in_city[day_idx][cidx["Hamburg"]], 1, 0)
    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)
    
    # Constraints for each day: must be in 1 or 2 cities, and if two, they must be adjacent
    for day_idx in range(num_days):
        m, b, h = in_city[day_idx][cidx["Mykonos"]], in_city[day_idx][cidx["Budapest"]], in_city[day_idx][cidx["Hamburg"]]
        num_present = If(m, 1, 0) + If(b, 1, 0) + If(h, 1, 0)
        s.add(Or(num_present == 1, num_present == 2))
        
        # Adjacent pairs: (Mykonos and Budapest) or (Budapest and Hamburg)
        s.add(Implies(num_present == 2, Or(And(m, b), And(b, h))))
    
    # Continuity constraints: consecutive days must share at least one city
    for day_idx in range(num_days - 1):
        m1, b1, h1 = in_city[day_idx][cidx["Mykonos"]], in_city[day_idx][cidx["Budapest"]], in_city[day_idx][cidx["Hamburg"]]
        m2, b2, h2 = in_city[day_idx+1][cidx["Mykonos"]], in_city[day_idx+1][cidx["Budapest"]], in_city[day_idx+1][cidx["Hamburg"]]
        s.add(Or(And(m1, m2), And(b1, b2), And(h1, h2)))
    
    # Solve
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day_idx in range(num_days):
            day_number = day_idx + 1
            present_cities = []
            for city in cities:
                if is_true(model[in_city[day_idx][cidx[city]]]):
                    present_cities.append(city)
            present_cities.sort()
            place_str = ", ".join(present_cities)
            itinerary_list.append({"day": day_number, "place": place_str})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()