import json

def main():
    total_days = 9
    days_per_city = {
        "Hamburg": 2,
        "Budapest": 3,
        "Mykonos": 6
    }
    
    start_hamburg = 1
    end_hamburg = start_hamburg + days_per_city["Hamburg"] - 1
    
    start_budapest = end_hamburg
    end_budapest = start_budapest + days_per_city["Budapest"] - 1
    
    start_mykonos = end_budapest
    end_mykonos = start_mykonos + days_per_city["Mykonos"] - 1
    
    itinerary = [
        {"day_range": f"Day {start_hamburg}-{end_hamburg}", "place": "Hamburg"},
        {"day_range": f"Day {start_budapest}-{end_budapest}", "place": "Budapest"},
        {"day_range": f"Day {start_mykonos}-{end_mykonos}", "place": "Mykonos"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()