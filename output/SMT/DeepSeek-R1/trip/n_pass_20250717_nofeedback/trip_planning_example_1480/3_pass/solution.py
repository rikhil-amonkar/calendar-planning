from z3 import *

def main():
    cities = ["Geneva", "Istanbul", "Venice", "Munich", "Reykjavik", "Madrid", "Vienna", "Vilnius", "Brussels"]
    n = len(cities)
    s = Solver()
    
    # Order variables: permutation of cities
    order = [Int(f'order_{i}') for i in range(n)]
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Start and end days (end day is exclusive)
    starts = [Int(f'start_{i}') for i in range(n)]
    ends = [Int(f'end_{i}') for i in range(n)]  # ends[i] is first day after stay
    
    # First city starts on day 1, last ends on day 28 (to cover day 27 inclusive)
    s.add(starts[0] == 1)
    s.add(ends[n-1] == 28)
    
    # Duration constraints: 2-4 days per segment
    for i in range(n):
        duration = ends[i] - starts[i]
        s.add(duration >= 2, duration <= 4)
    
    # Consecutive segments: end[i] == start[i+1]
    for i in range(n-1):
        s.add(ends[i] == starts[i+1])
    
    # Total trip must be 27 days
    s.add(Sum([ends[i] - starts[i] for i in range(n)]) == 27)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            city_idx = m.evaluate(order[i]).as_long()
            start_day = m.evaluate(starts[i]).as_long()
            end_exclusive = m.evaluate(ends[i]).as_long()
            end_inclusive = end_exclusive - 1  # convert to inclusive
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_inclusive}",
                'place': cities[city_idx]
            })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()