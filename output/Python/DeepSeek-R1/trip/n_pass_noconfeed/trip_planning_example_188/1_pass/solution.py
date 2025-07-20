import json

def format_day_range(start, end):
    if start == end:
        return f"Day {start}"
    else:
        return f"Day {start}-{end}"

def main():
    total_days = 12
    brussels_days = 2
    barcelona_days = 7
    split_days = 5
    
    start_brussels = 1
    end_brussels = start_brussels + brussels_days - 1
    
    start_barcelona = end_brussels
    end_barcelona = start_barcelona + barcelona_days - 1
    
    start_split = end_barcelona
    end_split = start_split + split_days - 1
    
    if end_split > total_days:
        raise ValueError("Total days exceeded with given constraints")
    
    itinerary = [
        {"day_range": format_day_range(start_brussels, end_brussels), "place": "Brussels"},
        {"day_range": format_day_range(start_barcelona, end_barcelona), "place": "Barcelona"},
        {"day_range": format_day_range(start_split, end_split), "place": "Split"}
    ]
    
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()