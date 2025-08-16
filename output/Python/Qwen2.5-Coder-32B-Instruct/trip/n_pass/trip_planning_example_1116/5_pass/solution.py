import json
from itertools import permutations

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

    def can_stay_in_city(city, start_day, days_needed):
        fixed_days = constraints[city].get("fixed_days", [])
        if not fixed_days:
            return start_day + days_needed - 1 <= 30
        for fixed_start, fixed_end in fixed_days:
            if fixed_start <= start_day <= fixed_end and fixed_start <= start_day + days_needed - 1 <= fixed_end:
                return True
        return False

    def find_itinerary():
        cities = list(constraints.keys())
        for city_order in permutations(cities):
            itinerary = []
            current_day = 1
            valid = True
            for city in city_order:
                days_needed = constraints[city]["days"]
                valid_start_day = None
                for start_day in range(current_day, 31 - days_needed + 1):
                    if can_stay_in_city(city, start_day, days_needed):
                        if itinerary:
                            prev_city = itinerary[-1]["place"]
                            if not is_valid_move(prev_city, city):
                                continue
                        valid_start_day = start_day
                        break
                if valid_start_day is not None:
                    end_day = valid_start_day + days_needed - 1
                    itinerary.append({"day_range": f"Day {valid_start_day}-{end_day}", "place": city})
                    current_day = end_day + 1
                else:
                    valid = False
                    break
            if valid:
                return itinerary
        raise ValueError("No valid itinerary found")

    itinerary = find_itinerary()
    return json.dumps({"itinerary": itinerary})

print(calculate_itinerary())