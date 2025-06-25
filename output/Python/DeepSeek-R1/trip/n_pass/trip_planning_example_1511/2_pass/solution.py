import json

def main():
    cities = [
        "Tallinn",
        "Munich",
        "Manchester",
        "Santorini",
        "Venice",
        "Vienna",
        "Valencia",
        "Porto",
        "Bucharest",
        "Reykjavik"
    ]
    
    # Durations for each city (sums to 24 days)
    durations = [3, 2, 2, 2, 3, 5, 2, 3, 1, 1]
    
    itinerary = []
    current_day = 1
    for idx, city in enumerate(cities):
        duration = durations[idx]
        end_day = current_day + duration - 1
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()