import json

def main():
    total_days = 12
    city_days = {
        "Naples": 3,
        "Seville": 4,
        "Milan": 7
    }
    fixed_period = {
        "city": "Seville",
        "start": 9,
        "end": 12
    }
    
    total_city_days = sum(city_days.values())
    travel_days = total_city_days - total_days
    if travel_days != 2:
        raise ValueError(f"Inconsistent travel days: computed {travel_days}, expected 2.")
    
    travel_day1 = city_days["Naples"]
    travel_day2 = fixed_period["start"]
    
    milan_stay_days = travel_day2 - travel_day1 + 1
    if milan_stay_days != city_days["Milan"]:
        raise ValueError(f"Milan stay mismatch: computed {milan_stay_days} days, expected {city_days['Milan']}.")
    
    itinerary = [
        {"day_range": f"Day 1-{travel_day1}", "place": "Naples"},
        {"day_range": f"Day {travel_day1}-{travel_day2}", "place": "Milan"},
        {"day_range": f"Day {travel_day2}-{fixed_period['end']}", "place": fixed_period["city"]}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()