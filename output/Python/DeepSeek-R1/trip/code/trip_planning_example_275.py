import json

def main():
    required_days = {
        'Split': 5,
        'Vilnius': 4,
        'Santorini': 2,
        'Madrid': 6
    }
    conference_start = 13
    conference_end = 14
    
    santorini_start = conference_start
    santorini_end = conference_end
    
    madrid_end = santorini_start
    madrid_start = madrid_end - required_days['Madrid'] + 1
    
    split_end = madrid_start
    split_start = split_end - required_days['Split'] + 1
    
    vilnius_end = split_start
    vilnius_start = vilnius_end - required_days['Vilnius'] + 1
    
    itinerary = [
        {"day_range": f"Day {vilnius_start}-{vilnius_end}", "place": "Vilnius"},
        {"day_range": f"Day {split_start}-{split_end}", "place": "Split"},
        {"day_range": f"Day {madrid_start}-{madrid_end}", "place": "Madrid"},
        {"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"}
    ]
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()