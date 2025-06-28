import json

def main():
    total_days = 12
    naples_days = 3
    seville_days = 4
    milan_days = 7
    seville_start = 9
    seville_end = 12

    travel_day_naples_milan = naples_days
    milan_start = travel_day_naples_milan
    milan_end = seville_start

    itinerary = [
        {"day_range": f"Day 1-{naples_days}", "place": "Naples"},
        {"day_range": f"Day {milan_start}-{milan_end}", "place": "Milan"},
        {"day_range": f"Day {seville_start}-{seville_end}", "place": "Seville"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()