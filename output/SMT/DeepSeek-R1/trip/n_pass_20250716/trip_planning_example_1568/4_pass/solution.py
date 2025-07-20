def main():
    # Define the cities with their durations in the new order
    cities = [
        ("Vienna", 4),
        ("Istanbul", 1),
        ("Prague", 4),
        ("Munich", 1),
        ("Split", 2),
        ("Amsterdam", 2),
        ("Riga", 1),
        ("Stockholm", 1),
        ("Brussels", 1),
        ("Seville", 3)
    ]
    
    itinerary = []
    current_day = 1
    
    for city, duration in cities:
        if duration == 1:
            day_range = f"Day {current_day}"
            end_day = current_day
        else:
            end_day = current_day + duration - 1
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()