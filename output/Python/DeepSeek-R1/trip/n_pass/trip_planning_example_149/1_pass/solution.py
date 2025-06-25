import json

def main():
    total_days = 10
    london_stay = 3
    santorini_stay = 6
    istanbul_stay = 3
    
    # Santorini must cover day 5 and day 10, and requires 6 contiguous days
    santorini_start = 5
    santorini_end = santorini_start + santorini_stay - 1  # 5+6-1=10
    
    # London segment must end on the day Santorini starts (due to travel on that day)
    london_end = santorini_start
    london_start = london_end - london_stay + 1  # 5-3+1=3
    
    # Istanbul segment must end on the day London starts (due to travel on that day)
    istanbul_end = london_start  # 3
    istanbul_start = istanbul_end - istanbul_stay + 1  # 3-3+1=1
    
    itinerary = [
        {"day_range": f"Day {istanbul_start}-{istanbul_end}", "place": "Istanbul"},
        {"day_range": f"Day {london_start}-{london_end}", "place": "London"},
        {"day_range": f"Day {santorini_start}-{santorini_end}", "place": "Santorini"}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()