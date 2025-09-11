import json

def main():
    total_days = 16
    cities = {
        "Split": {"days": 5, "show": (7, 11)},
        "Oslo": {"days": 2},
        "London": {"days": 7, "relatives": (1, 7)},
        "Porto": {"days": 5}
    }
    direct_flights = [("London", "Oslo"), ("Split", "Oslo"), ("Oslo", "Porto"), ("London", "Split")]
    
    order = ["London", "Split", "Oslo", "Porto"]
    start_day = 1
    itinerary_list = []
    
    for city in order:
        duration = cities[city]["days"]
        end_day = start_day + duration - 1
        itinerary_list.append({
            "day_range": f"Day {start_day}-{end_day}",
            "place": city
        })
        start_day = end_day
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()