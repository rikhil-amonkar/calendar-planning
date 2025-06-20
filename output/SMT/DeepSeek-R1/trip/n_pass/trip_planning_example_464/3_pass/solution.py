def create_itinerary(events, total_days=18):
    cities_set = set(event['city'] for event in events)
    city_intervals = {}
    for city in cities_set:
        city_events = [e for e in events if e['city'] == city]
        min_start = min(event['start'] for event in city_events)
        max_end = max(event['end'] for event in city_events)
        city_intervals[city] = {'min_start': min_start, 'max_end': max_end}
    
    city_list = []
    for city, interval in city_intervals.items():
        city_list.append((interval['min_start'], interval['max_end'], city))
    
    city_list.sort(key=lambda x: (x[0], x[1]))
    
    itinerary = []
    current_day = 1
    
    for min_start, max_end, city in city_list:
        if current_day > min_start:
            return {'itinerary': []}
        if current_day > max_end:
            return {'itinerary': []}
        
        segment_end = max_end
        if max_end > total_days:
            segment_end = total_days
        
        if current_day == segment_end:
            day_range_str = f"Day {current_day}"
        else:
            day_range_str = f"Day {current_day}-{segment_end}"
        itinerary.append({'day_range': day_range_str, 'place': city})
        
        current_day = segment_end + 1
        if current_day > total_days:
            break
    
    if current_day <= total_days:
        return {'itinerary': []}
    
    return {'itinerary': itinerary}