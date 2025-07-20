import json

def main():
    total_days = 17
    stay_naples = 5
    stay_vienna = 7
    stay_vilnius = 7

    naples_start = 1
    naples_end = naples_start + stay_naples - 1

    vienna_start = naples_end
    vienna_end = vienna_start + stay_vienna - 1

    vilnius_start = vienna_end
    vilnius_end = total_days

    itinerary = [
        {"day_range": f"Day {naples_start}-{naples_end}", "place": "Naples"},
        {"day_range": f"Day {vienna_start}-{vienna_end}", "place": "Vienna"},
        {"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()