import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'London': 7,
            'Oslo': 2,
            'Split': 5,
            'Porto': 5
        }
        self.fixed_stays = {
            'London': (7, 1, 7),
            'Split': (5, 7, 11)
        }
        self.flights = {
            'London': ['Oslo', 'Split'],
            'Oslo': ['Split', 'Porto'],
            'Split': ['Porto'],
            'Porto': []
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'London'  # Start with London to visit relatives

        # London stay
        london_days = self.cities['London']
        itinerary.append({'day_range': f'Day 1-{london_days}', 'place': 'London'})
        current_day += london_days

        # Fly to Oslo
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'London', 'to': 'Oslo'})
        current_day += 1

        # Oslo stay
        oslo_days = self.cities['Oslo']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + oslo_days - 1}', 'place': 'Oslo'})
        current_day += oslo_days

        # Fly to Split
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Split'})
        current_day += 1

        # Split stay
        split_days = self.cities['Split']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + split_days - 1}', 'place': 'Split'})
        current_day += split_days

        # Fly to Porto
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Split', 'to': 'Porto'})
        current_day += 1

        # Porto stay
        porto_days = self.cities['Porto']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + porto_days - 1}', 'place': 'Porto'})
        current_day += porto_days

        return itinerary

planner = TripPlanner()
itinerary = planner.compute_itinerary()

# Adjusting the day ranges to match the required format
for item in itinerary:
    if 'day_range' in item:
        days = item['day_range'].split('-')
        start_day = days[1]
        end_day = days[2] if len(days) > 2 else start_day
        item['day_range'] = f'Day {start_day}-{end_day}'
    elif 'flying' in item:
        flying_day = item['flying'].split('-')[1]
        item['flying'] = f'Day {flying_day}'

print(json.dumps(itinerary, indent=2))