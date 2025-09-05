import json
from z3 import *

def duration(city):
    # Returns the required number of days for the given city.
    # City encoding: 0 = Vilnius, 1 = Split, 2 = Madrid, 3 = Santorini
    return If(city == 0, 4, If(city == 1, 5, If(city == 2, 6, If(city == 3, 2, 0))))

def allowed_flight(a, b):
    # Returns a Z3 boolean constraint that a direct flight exists between city a and city b
    # Flights exist between Vilnius and Split, Split and Madrid, and Madrid and Santorini (bidirectional)
    return Or(And(a == 0, b == 1), And(a == 1, b == 0),
              And(a == 1, b == 2), And(a == 2, b == 1),
              And(a == 2, b == 3), And(a == 3, b == 2))

def main():
    solver = Solver()
    
    # Define itinerary segments: each segment is a visit to one city.
    # We have 4 segments (cities) for a trip of 14 calendar days.
    s0 = Int('s0')
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    
    # Constrain each segment city to be one of the 4 cities (0,1,2,3)
    solver.add(Or(s0 == 0, s0 == 1, s0 == 2, s0 == 3))
    solver.add(Or(s1 == 0, s1 == 1, s1 == 2, s1 == 3))
    solver.add(Or(s2 == 0, s2 == 1, s2 == 2, s2 == 3))
    solver.add(Or(s3 == 0, s3 == 1, s3 == 2, s3 == 3))
    
    # Ensure each city is visited exactly once.
    solver.add(Distinct(s0, s1, s2, s3))
    
    # Conference constraint: Days 13 and 14 must be in Santorini.
    # Force the last visited city to be Santorini.
    solver.add(s3 == 3)
    
    # Calculate the required day durations based on the city visited.
    d0 = duration(s0)
    d1 = duration(s1)
    d2 = duration(s2)
    d3 = duration(s3)
    
    # The sum of allocated city-days (overlapping flight days count twice)
    # must equal 17, because: 4 + 5 + 6 + 2 = 17.
    solver.add(d0 + d1 + d2 + d3 == 17)
    
    # Total calendar days = total allocated days - (number of flights)
    # We take 3 flights (between 4 segments) so:
    solver.add((d0 + d1 + d2 + d3) - 3 == 14)
    
    # Flight transitions constraints: if you fly from one city to the next,
    # there must be a direct flight between them.
    solver.add(allowed_flight(s0, s1))
    solver.add(allowed_flight(s1, s2))
    solver.add(allowed_flight(s2, s3))
    
    # Calculate the start day of each segment.
    # The rule is: if you fly on a day, that day counts for both departure and arrival.
    # Let:
    #   day_start[0] = 1,
    #   day_end[0]   = d0.
    # For i >= 1:
    #   day_start[i] = day_end[i-1] (flight day overlap)
    #   day_end[i]   = day_start[i] + d[i] - 1.
    # The last segment (segment 3) then occupies:
    #   day_start[3] = d0 + d1 + d2 - 2  and day_end[3] = (d0+d1+d2+d3) - 3.
    # To attend the conference on days 13 and 14, we must have:
    solver.add(d0 + d1 + d2 - 2 == 13)
    
    # Try to solve the constraints.
    if solver.check() == sat:
        model = solver.model()
        itinerary_cities = [
            model[s0].as_long(),
            model[s1].as_long(),
            model[s2].as_long(),
            model[s3].as_long()
        ]
        
        # Use the fixed durations from the problem statement:
        # Vilnius: 4, Split: 5, Madrid: 6, Santorini: 2.
        city_durations = {0: 4, 1: 5, 2: 6, 3: 2}
        durations = [city_durations[city] for city in itinerary_cities]

        # Compute calendar day ranges.
        day_starts = [0] * 4
        day_ends = [0] * 4
        day_starts[0] = 1
        day_ends[0] = durations[0]  # Segment 0: days 1 to d0.
        for i in range(1, 4):
            day_starts[i] = day_ends[i-1]  # Flight day overlap.
            day_ends[i] = day_starts[i] + durations[i] - 1

        city_names = {0: "Vilnius", 1: "Split", 2: "Madrid", 3: "Santorini"}
        itinerary = []
        for i in range(4):
            itinerary.append({
                "day_range": "Day {}-{}".format(day_starts[i], day_ends[i]),
                "place": city_names[itinerary_cities[i]]
            })
            
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        # If no solution is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()