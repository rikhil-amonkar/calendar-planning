import json

def main():
    # Fixed constraints
    total_days = 18
    cities = {
        "Bucharest": {"days": 4, "window": (1, 4)},
        "Munich": {"days": 5, "window": (4, 8)},
        "Seville": {"days": 5, "window": (8, 12)},
        "Tallinn": {"days": 2, "window": None},
        "Stockholm": {"days": 5, "window": None},
        "Milan": {"days": 2, "window": None}
    }
    
    # Direct flights graph
    graph = {
        "Milan": ["Stockholm", "Munich", "Seville"],
        "Stockholm": ["Milan", "Munich", "Tallinn"],
        "Munich": ["Stockholm", "Bucharest", "Seville", "Milan", "Tallinn"],
        "Bucharest": ["Munich"],
        "Seville": ["Munich", "Milan"],
        "Tallinn": ["Stockholm", "Munich"]
    }
    
    # Since the fixed events force the first 12 days, we compute the itinerary accordingly
    itinerary = []
    current_day = 1
    
    # Bucharest segment (days 1-4)
    Bucharest_end = current_day + cities["Bucharest"]["days"] - 1
    itinerary.append({"day_range": f"Day {current_day}-{Bucharest_end}", "place": "Bucharest"})
    current_day = Bucharest_end  # travel on day 4 to Munich
    
    # Munich segment (days 4-8)
    Munich_end = current_day + cities["Munich"]["days"] - 1
    itinerary.append({"day_range": f"Day {current_day}-{Munich_end}", "place": "Munich"})
    current_day = Munich_end  # travel on day 8 to Seville
    
    # Seville segment (days 8-12)
    Seville_end = current_day + cities["Seville"]["days"] - 1
    itinerary.append({"day_range": f"Day {current_day}-{Seville_end}", "place": "Seville"})
    current_day = Seville_end  # travel on day 12 to Milan
    
    # Remaining cities: Milan, Stockholm, Tallinn
    # Using direct flights: Seville -> Milan -> Stockholm -> Tallinn
    remaining_cities = [
        {"name": "Milan", "days": 2},
        {"name": "Stockholm", "days": 5},
        {"name": "Tallinn", "days": 2}
    ]
    
    for city_info in remaining_cities:
        city = city_info["name"]
        days_needed = city_info["days"]
        start_day = current_day
        end_day = current_day + days_needed - 1
        itinerary.append({"day_range": f"Day {start_day}-{end_day}", "place": city})
        current_day = end_day  # travel on the last day to next city

    # Output the itinerary as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()