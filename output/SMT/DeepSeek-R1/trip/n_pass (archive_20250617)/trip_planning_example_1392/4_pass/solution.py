from z3 import *

def main():
    cities = ['Naples', 'Valencia', 'Stuttgart', 'Split', 'Venice', 'Amsterdam', 'Nice', 'Barcelona', 'Porto']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    flight_pairs = [
        ("Venice", "Nice"), ("Naples", "Amsterdam"), ("Barcelona", "Nice"), ("Amsterdam", "Nice"),
        ("Stuttgart", "Valencia"), ("Stuttgart", "Porto"), ("Split", "Stuttgart"), ("Split", "Naples"),
        ("Valencia", "Amsterdam"), ("Barcelona", "Porto"), ("Valencia", "Naples"), ("Venice", "Amsterdam"),
        ("Barcelona", "Naples"), ("Barcelona", "Valencia"), ("Split", "Amsterdam"), ("Barcelona", "Venice"),
        ("Stuttgart", "Amsterdam"), ("Naples", "Nice"), ("Venice", "Stuttgart"), ("Split", "Barcelona"),
        ("Porto", "Nice"), ("Barcelona", "Stuttgart"), ("Venice", "Naples"), ("Porto", "Amsterdam"),
        ("Porto", "Valencia"), ("Stuttgart", "Naples"), ("Barcelona", "Amsterdam")
    ]
    
    directed_edges = set()
    for a, b in flight_pairs:
        a_idx = city_map[a]
        b_idx = city_map[b]
        directed_edges.add((a_idx, b_idx))
        directed_edges.add((b_idx, a_idx))
    directed_edges = list(directed_edges)
    
    s = Solver()
    
    start_city = [Int(f'start_city_{i+1}') for i in range(24)]
    next_city = [Int(f'next_city_{i+1}') for i in range(24)]
    
    for i in range(24):
        s.add(start_city[i] >= 0, start_city[i] < 9)
        s.add(next_city[i] >= 0, next_city[i] < 9)
    
    for i in range(23):
        s.add(start_city[i+1] == next_city[i])
    
    for i in range(24):
        travel_condition = (start_city[i] != next_city[i])
        flight_options = []
        for (a, b) in directed_edges:
            flight_options.append(And(start_city[i] == a, next_city[i] == b))
        s.add(If(travel_condition, Or(flight_options), True))
    
    travel_days = Sum([If(start_city[i] != next_city[i], 1, 0) for i in range(24)])
    s.add(travel_days == 8)
    
    totals = [3, 5, 2, 5, 5, 4, 2, 2, 4]
    for c in range(9):
        total_c = 0
        for i in range(24):
            total_c += If(start_city[i] == c, 1, 0)
            total_c += If(And(start_city[i] != next_city[i], next_city[i] == c), 1, 0)
        s.add(total_c == totals[c])
    
    # Stricter constraints: Must have at least one full stay day in the city for meetings
    naples_days = []
    for day in [16, 17, 18]:  # Days 17, 18, 19 (0-indexed)
        in_naples = And(start_city[day] == city_map['Naples'], next_city[day] == city_map['Naples'])
        naples_days.append(in_naples)
    s.add(Or(naples_days))
    
    venice_days = []
    for day in [5, 6, 7, 8, 9]:  # Days 6-10 (0-indexed)
        in_venice = And(start_city[day] == city_map['Venice'], next_city[day] == city_map['Venice'])
        venice_days.append(in_venice)
    s.add(Or(venice_days))
    
    nice_days = []
    for day in [22, 23]:  # Days 23-24 (0-indexed)
        in_nice = And(start_city[day] == city_map['Nice'], next_city[day] == city_map['Nice'])
        nice_days.append(in_nice)
    s.add(Or(nice_days))
    
    barcelona_days = []
    for day in [4, 5]:  # Days 5-6 (0-indexed)
        in_barcelona = And(start_city[day] == city_map['Barcelona'], next_city[day] == city_map['Barcelona'])
        barcelona_days.append(in_barcelona)
    s.add(Or(barcelona_days))
    
    if s.check() == sat:
        model = s.model()
        schedule = []
        for i in range(24):
            start_val = model.evaluate(start_city[i]).as_long()
            next_val = model.evaluate(next_city[i]).as_long()
            if start_val == next_val:
                schedule.append(f"Day {i+1}: Stay in {cities[start_val]}")
            else:
                schedule.append(f"Day {i+1}: Travel from {cities[start_val]} to {cities[next_val]}")
        print("\n".join(schedule))
        
        city_days = {city: 0 for city in cities}
        for i in range(24):
            start_val = model.evaluate(start_city[i]).as_long()
            next_val = model.evaluate(next_city[i]).as_long()
            city_days[cities[start_val]] += 1
            if start_val != next_val:
                city_days[cities[next_val]] += 1
        print("\nTotal days per city:")
        for city in cities:
            print(f"{city}: {city_days[city]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()