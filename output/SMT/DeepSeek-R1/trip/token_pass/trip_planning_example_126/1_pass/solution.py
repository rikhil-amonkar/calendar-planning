from z3 import *
import json

def main():
    # Define the cities and their required days
    cities = ['Krakow', 'Paris', 'Seville']
    req_days = [5, 2, 6]  # Corresponding to cities order
    city_dict = {0: 'Krakow', 1: 'Paris', 2: 'Seville'}
    
    # Direct flights as allowed consecutive city pairs
    direct_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    # Segment city variables
    s1_city = Int('s1_city')
    s2_city = Int('s2_city')
    s3_city = Int('s3_city')
    
    # Duration variables for each segment
    d1 = Int('d1')
    d2 = Int('d2')
    d3 = Int('d3')
    
    solver = Solver()
    
    # Cities must be distinct and between 0 and 2
    solver.add(s1_city >= 0, s1_city <= 2)
    solver.add(s2_city >= 0, s2_city <= 2)
    solver.add(s3_city >= 0, s3_city <= 2)
    solver.add(Distinct(s1_city, s2_city, s3_city))
    
    # Durations must match required days for assigned city
    solver.add(d1 == req_days[s1_city])
    solver.add(d2 == req_days[s2_city])
    solver.add(d3 == req_days[s3_city])
    
    # Total logical days must be 13 (11 calendar days + 2 travel days)
    solver.add(d1 + d2 + d3 == 13)
    
    # Consecutive segments must have direct flights
    solver.add(Or([And(s1_city == i, s2_city == j) for (i, j) in direct_flights]))
    solver.add(Or([And(s2_city == i, s3_city == j) for (i, j) in direct_flights]))
    
    # Workshop constraint: Krakow must be in segment 1 (days 1-5)
    solver.add(s1_city == 0)
    
    if solver.check() == sat:
        model = solver.model()
        s1_val = model.evaluate(s1_city).as_long()
        s2_val = model.evaluate(s2_city).as_long()
        s3_val = model.evaluate(s3_city).as_long()
        d1_val = model.evaluate(d1).as_long()
        d2_val = model.evaluate(d2).as_long()
        d3_val = model.evaluate(d3).as_long()
        
        # Calculate day ranges for segments
        start1 = 1
        end1 = d1_val
        start2 = end1
        end2 = start2 + d2_val - 1
        start3 = end2
        end3 = start3 + d3_val - 1
        
        itinerary = [
            {"day_range": f"Day {start1}-{end1}", "place": city_dict[s1_val]},
            {"day_range": f"Day {start2}-{end2}", "place": city_dict[s2_val]},
            {"day_range": f"Day {start3}-{end3}", "place": city_dict[s3_val]}
        ]
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()