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
    
    # Start and end days (both inclusive)
    starts = [Int(f'start_{i}') for i in range(n)]
    ends = [Int(f'end_{i}') for i in range(n)]
    
    # First city starts on day 1, last ends on day 27
    s.add(starts[0] == 1)
    s.add(ends[n-1] == 27)
    
    # Duration constraints: 2-4 days per segment
    for i in range(n):
        duration = ends[i] - starts[i] + 1
        s.add(And(duration >= 2, duration <= 4))
    
    # Consecutive segments: next start = previous end + 1
    for i in range(n-1):
        s.add(ends[i] + 1 == starts[i+1])
    
    # Total trip must be 27 days
    s.add(Sum([ends[i] - starts[i] + 1 for i in range(n)]) == 27)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            city_idx = m.evaluate(order[i]).as_long()
            start_day = m.evaluate(starts[i]).as_long()
            end_day = m.evaluate(ends[i]).as_long()
            
            itinerary.append({
                'day_range': f"Day {start_day}-{end_day}",
                'place': cities[city_idx]
            })
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()