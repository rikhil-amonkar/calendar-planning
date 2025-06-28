import json

def main():
    total_days = 10
    venice_days = 6
    workshop_start = 5
    workshop_end = 10
    mykonos_days = 2
    vienna_days = 4

    segments = []
    current_start = 1

    end_mykonos = current_start + mykonos_days - 1
    segments.append(("Mykonos", current_start, end_mykonos))
    current_start = end_mykonos

    end_vienna = current_start + vienna_days - 1
    segments.append(("Vienna", current_start, end_vienna))
    current_start = end_vienna

    end_venice = current_start + venice_days - 1
    segments.append(("Venice", current_start, end_venice))

    itinerary_list = []
    for city, start, end in segments:
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()