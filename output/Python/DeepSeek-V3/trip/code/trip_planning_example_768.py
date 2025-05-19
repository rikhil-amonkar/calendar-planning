import json
from itertools import permutations

def find_valid_itinerary():
    # Define the constraints
    total_days = 16
    city_days = {
        'Mykonos': 4,
        'Nice': 3,
        'London': 2,
        'Copenhagen': 3,
        'Oslo': 5,
        'Tallinn': 4
    }
    
    # Conference in Nice on day 14 and 16
    conference_days = [14, 16]
    
    # Friend meeting in Oslo between day 10 and 14
    oslo_meeting_start = 10
    oslo_meeting_end = 14
    
    # Direct flights
    direct_flights = {
        'London': ['Copenhagen', 'Mykonos', 'Nice', 'Oslo'],
        'Copenhagen': ['London', 'Tallinn', 'Nice', 'Oslo'],
        'Tallinn': ['Copenhagen', 'Oslo'],
        'Mykonos': ['London', 'Nice'],
        'Oslo': ['Tallinn', 'Nice', 'London', 'Copenhagen'],
        'Nice': ['Oslo', 'London', 'Mykonos', 'Copenhagen']
    }
    
    # All cities to visit
    cities = list(city_days.keys())
    
    # Generate all possible permutations of the cities
    for perm in permutations(cities):
        # Check if the permutation is valid based on direct flights
        valid = True
        for i in range(len(perm) - 1):
            if perm[i+1] not in direct_flights[perm[i]]:
                valid = False
                break
        if not valid:
            continue
        
        # Try to assign days to this permutation
        itinerary = []
        current_day = 1
        remaining_days = city_days.copy()
        
        for city in perm:
            days_needed = remaining_days[city]
            
            # Check if the city is Nice and we need to accommodate conference days
            if city == 'Nice':
                # Nice must include day 14 and 16
                # We need to assign 3 days to Nice, including 14 and 16
                nice_days = [14, 16]
                # Find one more day around these days
                if 13 not in nice_days and (itinerary and itinerary[-1]['place'] != 'Nice'):
                    nice_days.append(13)
                elif 15 not in nice_days:
                    nice_days.append(15)
                nice_days.sort()
                if len(nice_days) != 3:
                    valid = False
                    break
                # Check if we can assign these days
                if nice_days[0] < current_day:
                    valid = False
                    break
                # Add preceding cities
                if current_day < nice_days[0]:
                    prev_days = nice_days[0] - current_day
                    if prev_days > 0:
                        prev_city = itinerary[-1]['place'] if itinerary else None
                        # Need to handle previous city days
                        # This is complex, so we'll skip for now and rely on permutation check
                        valid = False
                        break
                # Assign Nice days
                itinerary.append({'day_range': f'Day {nice_days[0]}-{nice_days[-1]}', 'place': 'Nice'})
                current_day = nice_days[-1] + 1
                remaining_days['Nice'] = 0
                continue
            
            # Check if the city is Oslo and we need to accommodate meeting between day 10 and 14
            if city == 'Oslo':
                # Oslo must include some days between 10 and 14
                # We need to assign 5 days to Oslo, with at least one day between 10 and 14
                oslo_start = max(current_day, oslo_meeting_start)
                oslo_end = oslo_start + 4  # 5 days total
                if oslo_end > oslo_meeting_end:
                    oslo_end = oslo_meeting_end
                    oslo_start = oslo_end - 4
                if oslo_start < current_day:
                    valid = False
                    break
                if oslo_end >= current_day + days_needed:
                    oslo_end = current_day + days_needed - 1
                # Check if the range is valid
                if oslo_end - oslo_start + 1 != days_needed:
                    valid = False
                    break
                itinerary.append({'day_range': f'Day {oslo_start}-{oslo_end}', 'place': 'Oslo'})
                current_day = oslo_end + 1
                remaining_days['Oslo'] = 0
                continue
            
            # For other cities, assign the required days
            end_day = current_day + days_needed - 1
            if end_day > total_days:
                valid = False
                break
            itinerary.append({'day_range': f'Day {current_day}-{end_day}', 'place': city})
            current_day = end_day + 1
            remaining_days[city] = 0
        
        # Check if all days are assigned and all cities are visited
        if valid and current_day > total_days and all(v == 0 for v in remaining_days.values()):
            # Now, add flight information
            final_itinerary = []
            for i in range(len(itinerary)):
                if i > 0:
                    from_city = itinerary[i-1]['place']
                    to_city = itinerary[i]['place']
                    fly_day = itinerary[i]['day_range'].split('-')[0].split(' ')[1]
                    final_itinerary.append({'flying': f'Day {fly_day}-{fly_day}', 'from': from_city, 'to': to_city})
                final_itinerary.append(itinerary[i])
            return final_itinerary
    
    return None

def main():
    itinerary = find_valid_itinerary()
    if itinerary:
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()