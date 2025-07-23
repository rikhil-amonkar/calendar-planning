import json

def main():
    total_days = 10
    krakow_days = 2
    wedding_start = 9
    wedding_end = 10
    dubrovnik_days = 7
    frankfurt_days = 3
    
    # Calculate the transition day from Dubrovnik to Frankfurt
    d = wedding_start - frankfurt_days + 1
    
    # Build the itinerary segments
    itinerary = [
        {"day_range": f"Day 1-{d}", "place": "Dubrovnik"},
        {"day_range": f"Day {d}-{wedding_start}", "place": "Frankfurt"},
        {"day_range": f"Day {wedding_start}-{wedding_end}", "place": "Krakow"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()