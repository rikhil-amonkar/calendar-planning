import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Geneva': 7,
            'Paris': 6,
            'Porto': 7,
            'Oslo': 5,
            'Reykjavik': 2
        }
        self.fixed_stays = {
            'Geneva': (7, 1, 7),
            'Oslo': (5, 19, 23)
        }
        self.flights = {
            'Geneva': ['Oslo', 'Paris', 'Porto'],
            'Paris': ['Oslo', 'Porto', 'Reykjavik'],
            'Porto': ['Paris', 'Oslo'],
            'Oslo': ['Geneva', 'Paris', 'Porto'],
            'Reykjavik': ['Paris', 'Oslo']
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = 'Geneva'  # Start with Geneva for the conference

        # Geneva stay
        geneva_days = self.cities['Geneva']
        itinerary.append({'day_range': f'Day 1-{geneva_days}', 'place': 'Geneva'})
        current_day += geneva_days

        # Fly to Paris
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Geneva', 'to': 'Paris'})
        current_day += 1

        # Paris stay
        paris_days = self.cities['Paris']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + paris_days - 1}', 'place': 'Paris'})
        current_day += paris_days

        # Fly to Porto
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Paris', 'to': 'Porto'})
        current_day += 1

        # Porto stay
        porto_days = self.cities['Porto']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + porto_days - 1}', 'place': 'Porto'})
        current_day += porto_days

        # Fly to Oslo
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Porto', 'to': 'Oslo'})
        current_day += 1

        # Oslo stay
        oslo_days = self.cities['Oslo']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + oslo_days - 1}', 'place': 'Oslo'})
        current_day += oslo_days

        # Fly to Reykjavik
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Oslo', 'to': 'Reykjavik'})
        current_day += 1

        # Reykjavik stay
        reykjavik_days = self.cities['Reykjavik']
        itinerary.append({'day_range': f'Day {current_day}-{current_day + reykjavik_days - 1}', 'place': 'Reykjavik'})
        current_day += reykjavik_days

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