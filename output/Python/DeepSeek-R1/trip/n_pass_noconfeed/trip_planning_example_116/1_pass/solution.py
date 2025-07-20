import json

def main():
    total_days = 18
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_days = [12, 18]
    
    santorini_start = min(conference_days)
    santorini_end = max(conference_days)
    if santorini_end - santorini_start + 1 != santorini_days:
        raise ValueError("Santorini days do not align with conference days")
    
    split_end = split_days
    london_start = split_end
    london_end = santorini_start
    
    if london_end - london_start + 1 != london_days:
        raise ValueError("London days do not fit within available days")
    
    itinerary = [
        {"day_range": f"Day 1-{split_end}", "place": "Split"},
        {"day_range": f"Day {london_start}-{london_end}", "place": "London"},
        {"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"}
    ]
    
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()