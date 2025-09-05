import json
from z3 import *

def main():
    s = Solver()

    # Number of segments in the itinerary
    n = 4

    # City encoding: 0 - Madrid, 1 - Paris, 2 - Bucharest, 3 - Seville
    # Fixed durations for each city:
    # Madrid: 7 days, Paris: 6 days, Bucharest: 2 days, Seville: 3 days
    durations = {0: 7, 1: 6, 2: 2, 3: 3}

    # Create SMT integer variables for each segment's start day and city.
    start_vars = [Int(f'start_{i}') for i in range(n)]
    city_vars = [Int(f'city_{i}') for i in range(n)]

    # Define a function to get the duration based on the city variable.
    def duration(city):
        return If(city == 0, durations[0],
                  If(city == 1, durations[1],
                     If(city == 2, durations[2],
                        If(city == 3, durations[3], 0))))

    # Compute the end day for each segment: end = start + duration - 1.
    end_vars = [start_vars[i] + duration(city_vars[i]) - 1 for i in range(n)]

    # Constraint: The trip starts on Day 1.
    s.add(start_vars[0] == 1)
    # For each subsequent segment, the start day equals the previous segment's end day.
    for i in range(1, n):
        s.add(start_vars[i] == end_vars[i-1])
    # The trip must end on Day 15.
    s.add(end_vars[n-1] == 15)

    # Constraint: Madrid must cover Day 1 to Day 7 (7 days in Madrid).
    # Force the first segment to be Madrid.
    s.add(city_vars[0] == 0)

    # Constraint: Bucharest must be visited for 2 days and be between day 14 and day 15.
    # The only possibility for a 2-day stay including day 15 is to start on day 14.
    # Force the last segment to be Bucharest.
    s.add(city_vars[n-1] == 2)
    s.add(start_vars[n-1] == 14)

    # All cities must be visited exactly once.
    s.add(Distinct(city_vars))

    # Define allowed flight transitions between cities.
    # Direct flights exist between:
    # Madrid & Paris, Madrid & Bucharest, Madrid & Seville,
    # Paris & Bucharest, Seville & Paris.
    def flight_allowed(c1, c2):
        return Or(
            # Any flight from/to Madrid is allowed as long as it's not to/from the same city.
            And(c1 == 0, c2 != 0),
            And(c2 == 0, c1 != 0),
            # Flights between Paris and Bucharest.
            And(c1 == 1, c2 == 2),
            And(c1 == 2, c2 == 1),
            # Flights between Paris and Seville.
            And(c1 == 1, c2 == 3),
            And(c1 == 3, c2 == 1)
        )

    # Add constraints for direct flight transitions between consecutive segments.
    for i in range(n - 1):
        s.add(flight_allowed(city_vars[i], city_vars[i+1]))

    # Solve the SMT problem.
    if s.check() == sat:
        m = s.model()
        # Map integers back to city names.
        city_names = {0: "Madrid", 1: "Paris", 2: "Bucharest", 3: "Seville"}
        itinerary = []
        for i in range(n):
            city_val = m.evaluate(city_vars[i]).as_long()
            start_day = m.evaluate(start_vars[i]).as_long()
            end_day = m.evaluate(end_vars[i]).as_long()
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": city_names[city_val]
            })
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()