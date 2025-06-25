def create_itinerary(events, total_days=18):
    city_intervals = {}
    for event in events:
        city = event['city']
        start = event['start']
        end = event['end']
        if city not in city_intervals:
            city_intervals[city] = {'min_start': start, 'max_end': end}
        else:
            if start < city_intervals[city]['min_start']:
                city_intervals[city]['min_start'] = start
            if end > city_intervals[city]['max_end']:
                city_intervals[city]['max_end'] = end
    
    cities_list = []
    for city, interval in city_intervals.items():
        cities_list.append((interval['min_start'], interval['max_end'], city))
    
    cities_list.sort(key=lambda x: (x[0], x[1]))
    
    itinerary = []
    current_day = 1
    
    for i, (min_start, max_end, city) in enumerate(cities_list):
        if current_day > min_start:
            return {'itinerary': []}
            
        if max_end > total_days:
            return {'itinerary': []}
        
        if i == len(cities_list) - 1:
            segment_end = total_days
        else:
            segment_end = max_end
        
        if current_day == segment_end:
            day_range_str = f"Day {current_day}"
        else:
            day_range_str = f"Day {current_day}-{segment_end}"
        itinerary.append({'day_range': day_range_str, 'place': city})
        
        if i < len(cities_list) - 1:
            travel_day = segment_end + 1
            if travel_day > total_days:
                return {'itinerary': []}
            itinerary.append({'day_range': f"Day {travel_day}", 'place': 'Travel'})
            current_day = travel_day + 1
        else:
            current_day = segment_end + 1
    
    if current_day != total_days + 1:
        return {'itinerary': []}
    
    return {'itinerary': itinerary}