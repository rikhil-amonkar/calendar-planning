from z3 import Solver, Int, sat

def main():
    cities = [
        {'name': 'London', 'min_days': 5},
        {'name': 'Split', 'min_days': 3},
        {'name': 'Oslo', 'min_days': 2},
        {'name': 'Porto', 'min_days': 4}
    ]
    num_cities = len(cities)
    s = Solver()
    
    # Create start and end day variables for each city
    start_days = [Int(f'start_{i}') for i in range(num_cities)]
    end_days = [Int(f'end_{i}') for i in range(num_cities)]
    
    # First city starts on Day 1
    s.add(start_days[0] == 1)
    
    # Last city ends on Day 16
    s.add(end_days[num_cities-1] == 16)
    
    # Continuity constraints with travel days
    for i in range(num_cities-1):
        # Next city starts 1 day after current city ends (accounting for travel)
        s.add(start_days[i+1] == end_days[i] + 1)
    
    # Minimum stay constraints
    for i in range(num_cities):
        min_days = cities[i]['min_days']
        s.add(end_days[i] - start_days[i] + 1 >= min_days)
        s.add(start_days[i] >= 1)
        s.add(end_days[i] <= 16)
        s.add(start_days[i] <= end_days[i])
    
    # Total days must sum to 16
    total_days = sum(end_days[i] - start_days[i] + 1 for i in range(num_cities))
    s.add(total_days == 16)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(num_cities):
            s_val = m[start_days[i]].as_long()
            e_val = m[end_days[i]].as_long()
            city = cities[i]['name']
            if s_val == e_val:
                day_range = f"Day {s_val}"
            else:
                day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': city})
        print(f"Plan found: {{'itinerary': {itinerary}}}")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()