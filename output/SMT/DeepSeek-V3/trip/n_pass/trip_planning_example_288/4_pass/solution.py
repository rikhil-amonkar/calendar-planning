from z3 import *
import json

def solve_itinerary():
    s = Solver()

    days = list(range(1, 16))  # Days 1 to 15
    cities = ['Manchester', 'Stuttgart', 'Madrid', 'Vienna']
    city_index = {city: idx for idx, city in enumerate(cities)}

    # Direct flight pairs (bidirectional)
    direct_flights = [
        ('Vienna', 'Stuttgart'),
        ('Manchester', 'Vienna'),
        ('Madrid', 'Vienna'),
        ('Manchester', 'Stuttgart'),
        ('Manchester', 'Madrid')
    ]
    flight_pairs = [(city_index[c1], city_index[c2]) for c1, c2 in direct_flights]
    flight_pairs += [(j, i) for i, j in flight_pairs]

    # Variables: day_flight[day][city] is True if the person is in city on that day.
    day_flight = [[Bool(f"day_{day}_city_{city}") for city in cities] for day in days]

    # Each day, the person is in at least one city.
    for day in days:
        s.add(Or(day_flight[day-1]))

    # If two cities are visited on the same day, they must be connected by a direct flight.
    for day in days:
        for c1 in range(len(cities)):
            for c2 in range(c1+1, len(cities)):
                both = And(day_flight[day-1][c1], day_flight[day-1][c2])
                s.add(Implies(both, Or([ (c1 == fc1 and c2 == fc2) for fc1, fc2 in flight_pairs ])))

    # Total days per city.
    s.add(Sum([If(day_flight[d][city_index['Manchester']], 1, 0) for d in range(15)]) == 7)
    s.add(Sum([If(day_flight[d][city_index['Stuttgart']], 1, 0) for d in range(15)]) == 5)
    s.add(Sum([If(day_flight[d][city_index['Madrid']], 1, 0) for d in range(15)]) == 4)
    s.add(Sum([If(day_flight[d][city_index['Vienna']], 1, 0) for d in range(15)]) == 2)

    # Manchester days 1-7: all 7 days must be in Manchester.
    for day in range(1, 8):
        s.add(day_flight[day-1][city_index['Manchester']])

    # Stuttgart days 11-15: all 5 days must be in Stuttgart.
    for day in range(11, 16):
        s.add(day_flight[day-1][city_index['Stuttgart']])

    # Solve.
    if s.check() == sat:
        m = s.model()
        itinerary = []

        for day in days:
            present_cities = [city for city_idx, city in enumerate(cities) if m.evaluate(day_flight[day-1][city_idx])]
            for city in present_cities:
                itinerary.append({"day_range": f"Day {day}", "place": city})

        # Now, group consecutive days for the same city.
        optimized = []
        i = 0
        n = len(itinerary)
        while i < n:
            current = itinerary[i]
            day = int(current['day_range'].split()[1])
            place = current['place']
            j = i + 1
            while j < n:
                next_entry = itinerary[j]
                next_day = int(next_entry['day_range'].split()[1])
                if next_entry['place'] == place and next_day == day + (j - i):
                    j += 1
                else:
                    break
            if j == i + 1:
                optimized.append({"day_range": f"Day {day}", "place": place})
            else:
                optimized.append({"day_range": f"Day {day}-{day + (j - i) - 1}", "place": place})
            i = j

        # Reinsert flight days (days with multiple cities) as separate entries.
        final_itinerary = []
        for day in days:
            present_cities = [city for city_idx, city in enumerate(cities) if m.evaluate(day_flight[day-1][city_idx])]
            if len(present_cities) > 1:
                for city in present_cities:
                    final_itinerary.append({"day_range": f"Day {day}", "place": city})
            else:
                # Check if this day is part of a range in optimized.
                pass
        # Merge single-city days from optimized and multi-city days from final_itinerary.
        # Alternatively, the initial itinerary already includes all days, so return that.
        return {"itinerary": itinerary}
    else:
        return {"error": "No solution found"}

result = solve_itinerary()
print(json.dumps(result, indent=2))