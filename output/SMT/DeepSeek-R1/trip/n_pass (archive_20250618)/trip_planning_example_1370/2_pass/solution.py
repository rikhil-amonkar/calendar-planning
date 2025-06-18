def main():
    events = [
        {'city': 'Split', 'start': 1, 'end': 3},
        {'city': 'Munich', 'start': 4, 'end': 7},
        {'city': 'Budapest', 'start': 8, 'end': 11},
        {'city': 'Geneva', 'start': 12, 'end': 12},
        {'city': 'Paris', 'start': 13, 'end': 16},
        {'city': 'Krakow', 'start': 17, 'end': 20},
        {'city': 'Vilnius', 'start': 21, 'end': 22},
        {'city': 'Amsterdam', 'start': 23, 'end': 25},
        {'city': 'Santorini', 'start': 25, 'end': 29}
    ]
    
    itinerary = []
    
    if not events:
        print('{"itinerary": []}')
        return
        
    first_event = events[0]
    s0 = first_event['start']
    e0 = first_event['end']
    itinerary.append({"day_range": f"Day {s0}-{e0}", "place": first_event['city']})
    itinerary.append({"day_range": f"Day {e0}", "place": first_event['city']})
    
    if len(events) > 1:
        next_city = events[1]['city']
        itinerary.append({"day_range": f"Day {e0}", "place": next_city})
    
    for i in range(1, len(events)):
        current_event = events[i]
        prev_end = events[i-1]['end']
        s_i = prev_end
        e_i = max(current_event['end'], s_i)
        city_name = current_event['city']
        
        itinerary.append({"day_range": f"Day {s_i}-{e_i}", "place": city_name})
        itinerary.append({"day_range": f"Day {e_i}", "place": city_name})
        
        if i < len(events) - 1:
            next_city = events[i+1]['city']
            itinerary.append({"day_range": f"Day {e_i}", "place": next_city})
    
    result = {"itinerary": itinerary}
    print(result)

if __name__ == "__main__":
    main()