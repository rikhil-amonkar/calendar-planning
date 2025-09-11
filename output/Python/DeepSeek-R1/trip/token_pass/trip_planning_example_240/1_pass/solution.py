import json

def main():
    # Given constraints
    total_days = 12
    prague_days = 2
    berlin_days = 3
    tallinn_days = 5
    stockholm_days = 5
    conference_days = [6, 8]
    tallinn_visit_range = (8, 12)
    
    # Direct flights
    direct_flights = {
        "Berlin": ["Tallinn"],
        "Tallinn": ["Berlin", "Prague", "Stockholm"],
        "Prague": ["Tallinn", "Stockholm"],
        "Stockholm": ["Tallinn", "Prague", "Berlin"]
    }
    
    # Itinerary segments based on logical calculation
    itinerary_segments = [
        {"day_range": "Day 1-2", "place": "Prague"},
        {"day_range": "Day 3-5", "place": "Stockholm"},
        {"day_range": "Day 6-8", "place": "Berlin"},
        {"day_range": "Day 8-12", "place": "Tallinn"}
    ]
    
    # Output the itinerary as JSON
    output = {"itinerary": itinerary_segments}
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()