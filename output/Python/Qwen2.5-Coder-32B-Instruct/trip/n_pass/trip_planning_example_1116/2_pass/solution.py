import json

def calculate_itinerary():
    constraints = {
        "Oslo": {"days": 2, "fixed_days": [(16, 17)]},
        "Reykjavik": {"days": 5, "fixed_days": [(9, 13)]},
        "Stockholm": {"days": 4, "fixed_days": []},
        "Munich": {"days": 4, "fixed_days": [(13, 16)]},
        "Frankfurt": {"days": 4, "fixed_days": [(17, 20)]},
        "Barcelona": {"days": 3, "fixed_days": []},
        "Bucharest": {"days": 2, "fixed_days": []},
        "Split": {"days": 3, "fixed_days": []}
    }

    direct_flights = [
        ("Reykjavik", "Munich"), ("Munich", "Frankfurt"), ("Split", "Oslo"),
        ("Reykjavik", "Oslo"), ("Bucharest", "Munich"), ("Oslo", "Frankfurt"),
        ("Bucharest", "Barcelona"), ("Barcelona", "Frankfurt"), ("Reykjavik", "Frankfurt"),
        ("Barcelona", "Stockholm"), ("Barcelona", "Reykjavik"), ("Stockholm", "Reykjavik"),
        ("Barcelona", "Split"), ("Bucharest", "Oslo"), ("Bucharest", "Frankfurt"),
        ("Split", "Stockholm"), ("Barcelona", "Oslo"), ("Stockholm", "Munich"),
        ("Stockholm", "Oslo"), ("Split", "Frankfurt"), ("Barcelona", "Munich"),
        ("Stockholm", "Frankfurt"), ("Munich", "Oslo"), ("Split", "Munich")
    ]

    def is_valid_move(city1, city2):
        return (city1, city2) in direct_flights or (city2, city1) in direct_flights

    def can_stay_in_city(city, day):
        fixed_days = constraints[city].get("fixed_days", [])
        if not fixed_days:
            return True
        for fixed_start, fixed_end in fixed_days:
            if fixed_start <= day <= fixed_end:
                return True
        return False

    def find_itinerary():
        itinerary = []
        current_day = 1
        remaining_cities = set(constraints.keys())

        while remaining_cities:
            found = False
            for city in sorted(remaining_cities, key=lambda x: constraints[x]["days"]):
                if can_stay_in_city(city, current_day):
                    start_day = current_day
                    end_day = start_day + constraints[city]["days"] - 1
                    valid = True
                    for d in range(start_day, end_day + 1):
                        if any(can_stay_in_city(c, d) for c in remaining_cities if c != city):
                            valid = False
                            break
                    if valid:
                        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
                        current_day = end_day + 1
                        remaining_cities.remove(city)
                        found = True
                        break
            if not found:
                raise ValueError("No valid itinerary found")

        return itinerary

    itinerary = find_itinerary()
    return json.dumps({"itinerary": itinerary})

print(calculate_itinerary())