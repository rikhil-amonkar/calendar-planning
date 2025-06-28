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
    
    # Durations: base 2 days per city, plus 1 extra day for Tallinn, Venice, Vienna, Porto
    durations = [
        3,  # Tallinn: 2 + 1
        2,  # Munich
        2,  # Manchester
        2,  # Santorini
        3,  # Venice: 2 + 1
        3,  # Vienna: 2 + 1
        2,  # Valencia
        3,  # Porto: 2 + 1
        2,  # Bucharest
        2   # Reykjavik
    ]
    
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