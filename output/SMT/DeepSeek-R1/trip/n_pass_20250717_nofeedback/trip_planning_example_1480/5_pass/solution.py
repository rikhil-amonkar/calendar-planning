from z3 import *

def main():
    cities = ["Geneva", "Istanbul", "Venice", "Munich", "Reykjavik", "Madrid", "Vienna", "Vilnius", "Brussels"]
    n = len(cities)
    total_days = 27
    s = Solver()
    
    # Position variables: position[i] = travel order index for each city
    position = [Int(f'pos_{city}') for city in cities]
    for i in range(n):
        s.add(position[i] >= 0, position[i] < n)
    s.add(Distinct(position))
    
    # Start day for each city
    start_day = [Int(f'start_{city}') for city in cities]
    for i in range(n):
        s.add(start_day[i] >= 1)
        s.add(start_day[i] <= total_days)
    
    # Duration for each city (2-4 days)
    duration = [Int(f'dur_{city}') for city in cities]
    for i in range(n):
        s.add(duration[i] >= 2)
        s.add(duration[i] <= 4)
    
    # End day for each city (start + duration - 1)
    end_day = [Int(f'end_{city}') for city in cities]
    for i in range(n):
        s.add(end_day[i] == start_day[i] + duration[i] - 1)
        s.add(end_day[i] <= total_days)
    
    # Timeline continuity constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                # Cities in different positions must not overlap
                i_before_j = position[i] < position[j]
                s.add(Implies(i_before_j, end_day[i] < start_day[j]))
                s.add(Implies(Not(i_before_j), end_day[j] < start_day[i]))
    
    # Consecutive position constraint
    for idx in range(n - 1):
        # Find which city is at position idx and next position idx+1
        at_position_idx = [And(position[i] == idx, position[j] == idx+1) for i in range(n) for j in range(n) if i != j]
        s.add(Or(at_position_idx))
        
        # Enforce consecutive stays: end of current = start of next - 1
        for i in range(n):
            for j in range(n):
                if i != j:
                    both_cond = And(position[i] == idx, position[j] == idx+1)
                    s.add(Implies(both_cond, end_day[i] == start_day[j] - 1))
    
    # Cover all days exactly
    all_days = [Bool(f'day_{d}') for d in range(1, total_days+1)]
    for d in range(1, total_days+1):
        covered = Or([And(start_day[i] <= d, d <= end_day[i]) for i in range(n)])
        s.add(covered)
    
    # Total days must be exactly 27
    s.add(Sum(duration) == total_days)
    
    # First day must be 1, last day must be 27
    s.add(Or([start_day[i] == 1 for i in range(n)]))
    s.add(Or([end_day[i] == total_days for i in range(n)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Collect all city stays
        stays = []
        for i, city in enumerate(cities):
            start = m.evaluate(start_day[i]).as_long()
            end = m.evaluate(end_day[i]).as_long()
            pos = m.evaluate(position[i]).as_long()
            stays.append((pos, start, end, city))
        
        # Sort by position
        stays.sort(key=lambda x: x[0])
        
        # Build itinerary
        for pos, start, end, city in stays:
            itinerary.append({
                'day_range': f"Day {start}-{end}",
                'place': city
            })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()