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
    
    stay_days = [
        3,  # Tallinn (minimum 2 days + 1 extra)
        1,  # Munich
        1,  # Manchester
        1,  # Santorini
        2,  # Venice (minimum 2 days)
        2,  # Vienna (minimum 2 days)
        1,  # Valencia
        2,  # Porto (minimum 2 days)
        1,  # Bucharest
        1   # Reykjavik
    ]
    
    itinerary = []
    current_day = 1
    n = len(cities)
    
    for i in range(n):
        stay = stay_days[i]
        end_stay = current_day + stay - 1
        
        if stay == 1:
            day_range_str = f"Day {current_day}"
        else:
            day_range_str = f"Day {current_day}-{end_stay}"
        
        itinerary.append({
            "day_range": day_range_str,
            "place": cities[i]
        })
        
        # Add travel day (1 day) after each city except last
        if i < n - 1:
            current_day = end_stay + 2
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()