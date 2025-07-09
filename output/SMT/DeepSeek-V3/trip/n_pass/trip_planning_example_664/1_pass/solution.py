from z3 import *

def solve_itinerary():
    s = Solver()

    cities = {
        "Tallinn": 2,
        "Bucharest": 4,
        "Seville": 5,
        "Stockholm": 5,
        "Munich": 5,
        "Milan": 2
    }

    direct_flights = {
        "Milan": ["Stockholm", "Munich"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }

    city_vars = {}
    for city in cities:
        start = Int(f'start_{city}')
        end = Int(f'end_{city}')
        city_vars[city] = (start, end)
        s.add(start >= 1)
        s.add(end <= 18)
        s.add(end == start + cities[city] - 1)

    # Bucharest between day 1 and 4
    s.add(city_vars["Bucharest"][0] >= 1)
    s.add(city_vars["Bucharest"][1] <= 4)

    # Munich between day 4 and 8
    s.add(city_vars["Munich"][0] >= 4)
    s.add(city_vars["Munich"][1] <= 8)

    # Seville between day 8 and 12
    s.add(city_vars["Seville"][0] >= 8)
    s.add(city_vars["Seville"][1] <= 12)

    city_list = list(cities.keys())
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1 = city_list[i]
            city2 = city_list[j]
            start1, end1 = city_vars[city1]
            start2, end2 = city_vars[city2]
            s.add(Or(
                end1 + 1 <= start2,
                end2 + 1 <= start1,
                And(end1 == start2, 
                    (city1 in direct_flights and city2 in direct_flights[city1]) or 
                    (city2 in direct_flights and city1 in direct_flights[city2])
                ),
                And(end2 == start1,
                    (city1 in direct_flights and city2 in direct_flights[city1]) or 
                    (city2 in direct_flights and city1 in direct_flights[city2])
                )
            ))

    if s.check() == sat:
        model = s.model()
        city_schedule = []
        for city in cities:
            start = model[city_vars[city][0]].as_long()
            end = model[city_vars[city][1]].as_long()
            city_schedule.append((start, end, city))
        
        city_schedule.sort(key=lambda x: x[0])

        itinerary = []
        prev_end = 0
        prev_city = None
        for start, end, city in city_schedule:
            if prev_end != 0:
                if prev_end == start:
                    itinerary.append({"day_range": f"Day {prev_end}", "place": prev_city})
                    itinerary.append({"day_range": f"Day {start}", "place": city})
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            prev_end = end
            prev_city = city

        # Verify total days
        unique_days = set()
        for entry in itinerary:
            day_range = entry["day_range"]
            if '-' in day_range:
                start, end = map(int, day_range.replace("Day ", "").split('-'))
                for day in range(start, end + 1):
                    unique_days.add(day)
            else:
                day = int(day_range.replace("Day ", ""))
                unique_days.add(day)
        assert len(unique_days) == 18, f"Total days is {len(unique_days)}, expected 18"

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))