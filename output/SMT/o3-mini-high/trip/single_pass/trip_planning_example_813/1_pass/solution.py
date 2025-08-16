from z3 import *
import json

# We'll encode each city by an integer:
#   0: Seville    (5 days)
#   1: Vilnius    (3 days)
#   2: Santorini  (2 days)
#   3: London     (2 days)
#   4: Stuttgart  (3 days)
#   5: Dublin     (3 days)
#   6: Frankfurt  (5 days)
#
# The overall “duration‐sum” is 5+3+2+2+3+3+5 = 23.
# Because flights “overlap” by one day between consecutive segments,
# the unique travel days are 23 – (7-1) = 17.

def duration(city):
    # returns the number of days spent in a city (including the flight day)
    return If(city == 0, 5,
           If(city == 1, 3,
           If(city == 2, 2,
           If(city == 3, 2,
           If(city == 4, 3,
           If(city == 5, 3,
              5))))))

# Define the allowed (direct) flight pairs (bidirectional)
def allowed_edge(x, y):
    return Or(And(x == 6, y == 5),   # Frankfurt <-> Dublin
              And(x == 5, y == 6),
              And(x == 6, y == 3),   # Frankfurt <-> London
              And(x == 3, y == 6),
              And(x == 3, y == 5),   # London <-> Dublin
              And(x == 5, y == 3),
              And(x == 1, y == 6),   # Vilnius <-> Frankfurt
              And(x == 6, y == 1),
              And(x == 6, y == 4),   # Frankfurt <-> Stuttgart
              And(x == 4, y == 6),
              And(x == 5, y == 0),   # Dublin <-> Seville
              And(x == 0, y == 5),
              And(x == 3, y == 2),   # London <-> Santorini
              And(x == 2, y == 3),
              And(x == 4, y == 3),   # Stuttgart <-> London
              And(x == 3, y == 4),
              And(x == 2, y == 5),   # Santorini <-> Dublin
              And(x == 5, y == 2))

# Main solver function
def solve_schedule():
    s = Solver()
    
    n = 7  # number of cities to visit
    
    # city[i] is the city visited in the i-th segment of the trip.
    # days[i] is the starting day of the segment (when you "land": note that if you take a flight on a day,
    # that day counts for both the previous and the next city).
    cities = [Int(f"city_{i}") for i in range(n)]
    days_vars = [Int(f"s_{i}") for i in range(n)]
    
    # City domain: 0..6. They must form a permutation.
    for i in range(n):
        s.add(And(cities[i] >= 0, cities[i] <= 6))
    s.add(Distinct(cities))
    
    # Day variables: They must be between 1 and 17.
    for i in range(n):
        s.add(And(days_vars[i] >= 1, days_vars[i] <= 17))
        
    # Set the starting day for the first city.
    s.add(days_vars[0] == 1)
    
    # The itinerary is built by “flights” that overlap on the day of change:
    # If you leave city A on day X to fly to city B, then A is visited until day X and B is visited starting on day X.
    # For every segment i (for i >= 1), we require:
    #   days[i] = days[i-1] + (duration(city[i-1]) - 1)
    for i in range(1, n):
        s.add(days_vars[i] == days_vars[i-1] + duration(cities[i-1]) - 1)
    
    # The final day of the trip is given by the last segment's end day:
    # days[n-1] + duration(city[n-1]) - 1 must equal 17.
    s.add(days_vars[n-1] + duration(cities[n-1]) - 1 == 17)
    
    # Between adjacent segments, we can only fly if there is a direct flight.
    for i in range(n - 1):
        s.add(allowed_edge(cities[i], cities[i+1]))
    
    # Additional scheduling constraints:
    # 1. London: You want to spend 2 days in London and want to meet your friends there
    #    between day 9 and day 10. Since London’s duration is 2 days, if its segment starts on day L,
    #    then the days in London are L and L+1. To include day 9 or 10, L must be between 8 and 10.
    for i in range(n):
        s.add(Implies(cities[i] == 3, And(days_vars[i] >= 8, days_vars[i] <= 10)))
    
    # 2. Stuttgart: You plan to stay in Stuttgart for 3 days and want to visit relatives there between day 7 and day 9.
    #    Stuttgart’s segment covers days s, s+1, s+2. To cover at least one day in [7,9], a sufficient constraint is:
    #    the segment must start no later than day 9 and no earlier than day 5 (since 5,6,7 would include day 7).
    for i in range(n):
        s.add(Implies(cities[i] == 4, And(days_vars[i] >= 5, days_vars[i] <= 9)))
    
    # (Other city durations are fixed by the plan/preferences:
    # Seville: 5 days, Vilnius: 3 days, Santorini: 2 days, Dublin: 3 days, Frankfurt: 5 days)
    #
    # Because the total summed duration is always 23, the overlapping flight days exactly yield 17 travel days.
    
    if s.check() == sat:
        m = s.model()
        
        # Map integer codes to city names.
        city_names = {
            0: "Seville",
            1: "Vilnius",
            2: "Santorini",
            3: "London",
            4: "Stuttgart",
            5: "Dublin",
            6: "Frankfurt"
        }
        
        # Retrieve the segments from the model.
        segments = []
        for i in range(n):
            c_val = m[cities[i]].as_long()
            start_day = m[days_vars[i]].as_long()
            # Use the same lookup as in duration():
            if c_val == 0 or c_val == 6:
                d = 5
            elif c_val in [1, 4, 5]:
                d = 3
            elif c_val in [2, 3]:
                d = 2
            else:
                d = 0
            segments.append({
                "city": city_names[c_val],
                "start": start_day,
                "end": start_day + d - 1  # inclusive end day
            })
        
        # Now, build a day-by-day itinerary.
        # A city segment covers all days from its start to end (and if the same day is an overlap, it is in two segments)
        itinerary_by_day = {}
        for day in range(1, 18):
            places = []
            for seg in segments:
                if seg["start"] <= day <= seg["end"]:
                    places.append(seg["city"])
            # On flight days the two overlapping cities are simply joined by a '/'
            itinerary_by_day[day] = "/".join(places)
        
        # Create a list of day->place mappings
        itinerary_list = []
        for day in range(1, 18):
            itinerary_list.append({"day": day, "place": itinerary_by_day[day]})
        
        result = {"itinerary": itinerary_list}
        # Print the JSON-formatted itinerary.
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    solve_schedule()