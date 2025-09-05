from z3 import *
import json

def main():
    # Create the Z3 solver instance
    solver = Solver()
    
    # We encode cities as integers:
    # 0: Dubrovnik (7 days stay)
    # 1: Frankfurt (3 days stay)
    # 2: Krakow   (2 days stay, wedding in Krakow must occur on day 9 or day 10)
    #
    # We have 3 segments corresponding to the order of visits:
    # seg1: days 1 to x, seg2: days x to y, seg3: days y to 10 (with overlaps on flight days).
    # Flight days (x and y) count for both the leaving and arriving cities.
    
    # Define segment city decision variables (domain: 0,1,2). They must be all distinct.
    seg1 = Int('seg1')
    seg2 = Int('seg2')
    seg3 = Int('seg3')
    
    # Flight transition days:
    x = Int('x')  # transition day between seg1 and seg2
    y = Int('y')  # transition day between seg2 and seg3

    # Domain constraints for city variables
    solver.add(And(seg1 >= 0, seg1 <= 2))
    solver.add(And(seg2 >= 0, seg2 <= 2))
    solver.add(And(seg3 >= 0, seg3 <= 2))
    solver.add(Distinct(seg1, seg2, seg3))
    
    # Wedding constraint: must attend wedding in Krakow between day 9 and day 10.
    # For simplicity, we force Krakow to be visited on the last segment.
    solver.add(seg3 == 2)
    
    # Direct flight constraints:
    # Allowed direct flights exist only between (Dubrovnik, Frankfurt) and (Frankfurt, Krakow).
    # Therefore, for flights between segments:
    #   - Flight from seg1 -> seg2 must be either (Dubrovnik, Frankfurt) or (Frankfurt, Dubrovnik).
    #   - Flight from seg2 -> seg3 must be between Frankfurt and Krakow.
    # Since seg3 is forced to Krakow (2), seg2 must be Frankfurt (1)
    solver.add(seg2 == 1)
    # With seg2 fixed to Frankfurt and seg3 fixed to Krakow,
    # seg1 must then be the remaining city: Dubrovnik (0)
    solver.add(seg1 == 0)
    
    # Required durations for each city:
    # Dubrovnik: 7 days, Frankfurt: 3 days, Krakow: 2 days.
    # We define the durations based on flight overlap:
    #   seg1: days 1 to x, so duration is x days.
    #   seg2: days x to y, so duration is (y - x + 1) days.
    #   seg3: days y to 10, so duration is (11 - y) days.
    #
    # If a segment is assigned a city, then its duration must equal the required number:
    #   if seg1 == 0, then x == 7
    #   if seg2 == 1, then y - x + 1 == 3
    #   if seg3 == 2, then 11 - y == 2
    solver.add(x == 7)
    solver.add(y - x + 1 == 3)
    solver.add(11 - y == 2)
    
    # Ensure the flight day variables are within the trip limits (1 to 10)
    solver.add(x >= 1, x <= 10)
    solver.add(y >= x, y <= 10)
    
    # Check for satisfiability
    if solver.check() == sat:
        model = solver.model()
        x_val = model[x].as_long()
        y_val = model[y].as_long()
        
        # Map integer codes to city names
        city_names = {0: "Dubrovnik", 1: "Frankfurt", 2: "Krakow"}
        
        itinerary = []
        # Segment 1: days 1 to x (Dubrovnik)
        itinerary.append({
            "day_range": "Day 1-" + str(x_val),
            "place": city_names[model[seg1].as_long()]
        })
        # Segment 2: days x to y (Frankfurt)
        itinerary.append({
            "day_range": "Day " + str(x_val) + "-" + str(y_val),
            "place": city_names[model[seg2].as_long()]
        })
        # Segment 3: days y to 10 (Krakow; includes wedding between day 9 and 10)
        itinerary.append({
            "day_range": "Day " + str(y_val) + "-10",
            "place": city_names[model[seg3].as_long()]
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == "__main__":
    main()