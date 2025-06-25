import json

def main():
    durations = {
        "Bucharest": 2,
        "Barcelona": 3,
        "Split": 3,
        "Stockholm": 4,
        "Reykjavik": 5,
        "Munich": 4,
        "Oslo": 2,
        "Frankfurt": 4
    }
    
    city_order = [
        "Bucharest",
        "Barcelona",
        "Split",
        "Stockholm",
        "Reykjavik",
        "Munich",
        "Oslo",
        "Frankfurt"
    ]
    
    current_start = 1
    itinerary_list = []
    
    for city in city_order:
        d = durations[city]
        end_day = current_start + d - 1
        day_range_str = f"Day {current_start}-{end_day}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": city
        })
        current_start = end_day
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()