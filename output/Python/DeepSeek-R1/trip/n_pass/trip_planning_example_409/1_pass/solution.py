import json

def main():
    total_days = 12
    wedding_interval = (1, 3)
    conference_interval = (4, 10)
    
    flights = {
        "Zurich": ["Helsinki", "Hamburg", "Bucharest", "Split"],
        "Helsinki": ["Zurich", "Hamburg", "Split"],
        "Hamburg": ["Helsinki", "Zurich", "Bucharest", "Split"],
        "Bucharest": ["Zurich", "Hamburg"],
        "Split": ["Zurich", "Helsinki", "Hamburg"]
    }
    
    non_zurich_cities = ["Helsinki", "Hamburg", "Bucharest"]
    
    for A in non_zurich_cities:
        if A not in flights["Zurich"]:
            continue
            
        remaining_cities = non_zurich_cities.copy()
        remaining_cities.remove(A)
        candidates_C = [city for city in remaining_cities if city in flights["Split"]]
        
        for C in candidates_C:
            remaining_after_C = [city for city in remaining_cities if city != C]
            if not remaining_after_C:
                continue
            D = remaining_after_C[0]
            if D not in flights.get(C, []):
                continue
                
            itinerary = [
                {"day_range": "Day 1-2", "place": A},
                {"day_range": "Day 2-4", "place": "Zurich"},
                {"day_range": "Day 4-10", "place": "Split"},
                {"day_range": "Day 10-11", "place": C},
                {"day_range": "Day 11-12", "place": D}
            ]
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
            
    print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()