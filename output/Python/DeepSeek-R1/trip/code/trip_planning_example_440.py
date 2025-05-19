import json

def main():
    city_days = {
        'Split': 2,
        'Helsinki': 2,
        'Reykjavik': 3,
        'Vilnius': 3,
        'Geneva': 6
    }
    
    flight_graph = {
        'Split': ['Helsinki', 'Geneva', 'Vilnius'],
        'Helsinki': ['Split', 'Geneva', 'Reykjavik', 'Vilnius'],
        'Geneva': ['Split', 'Helsinki'],
        'Reykjavik': ['Helsinki'],
        'Vilnius': ['Helsinki', 'Split']
    }
    
    itinerary = []
    current_day = 1
    
    # Assign Geneva first (6 days)
    geneva_end = current_day + city_days['Geneva'] - 1
    itinerary.append({
        'day_range': f"Day {current_day}-{geneva_end}",
        'place': 'Geneva'
    })
    current_day = geneva_end
    
    # Fly to Split (connected to Geneva)
    split_start = current_day
    split_end = split_start + city_days['Split'] - 1
    itinerary.append({
        'day_range': f"Day {split_start}-{split_end}",
        'place': 'Split'
    })
    current_day = split_end
    
    # Fly to Vilnius (connected to Split, must cover days 7-9)
    vilnius_start = current_day
    if vilnius_start > 7:
        raise ValueError("Vilnius constraint not met")
    vilnius_end = 9
    itinerary.append({
        'day_range': f"Day {vilnius_start}-{vilnius_end}",
        'place': 'Vilnius'
    })
    current_day = vilnius_end
    
    # Fly to Helsinki (connected to Vilnius)
    helsinki_start = current_day
    helsinki_end = helsinki_start + city_days['Helsinki'] - 1
    itinerary.append({
        'day_range': f"Day {helsinki_start}-{helsinki_end}",
        'place': 'Helsinki'
    })
    current_day = helsinki_end
    
    # Fly to Reykjavik (connected to Helsinki, must cover days 10-12)
    reykjavik_start = current_day
    if reykjavik_start > 10:
        raise ValueError("Reykjavik constraint not met")
    reykjavik_end = 12
    itinerary.append({
        'day_range': f"Day {reykjavik_start}-{reykjavik_end}",
        'place': 'Reykjavik'
    })
    
    print(json.dumps({'itinerary': itinerary}))

if __name__ == "__main__":
    main()