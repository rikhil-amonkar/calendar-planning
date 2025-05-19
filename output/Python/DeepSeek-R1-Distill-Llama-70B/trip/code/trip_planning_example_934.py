import json
from datetime import timedelta, date

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Brussels': 5,
            'Rome': 2,
            'Dubrovnik': 3,
            'Geneva': 5,
            'Budapest': 2,
            'Riga': 4,
            'Valencia': 2
        }
        self.fixed_stays = {
            'Riga': (4, 4, 7),
            'Brussels': (5, 7, 11),
            'Budapest': (2, 16, 17)
        }
        self.flights = {
            'Brussels': ['Valencia', 'Geneva', 'Budapest', 'Riga', 'Rome'],
            'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels'],
            'Dubrovnik': ['Geneva', 'Rome'],
            'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
            'Valencia': ['Brussels', 'Rome', 'Geneva'],
            'Budapest': ['Geneva', 'Riga', 'Brussels'],
            'Riga': ['Rome', 'Brussels']
        }

    def compute_itinerary(self):
        itinerary = []
        current_day = 1
        current_city = None

        # Start with Riga's fixed stay
        riga_start, riga_duration, riga_end = self.fixed_stays['Riga']
        # Need to reach Riga by day 4
        # Assume we start in Rome
        rome_days = min(2, 3)  # Adjust to fit before Riga
        itinerary.append({'day_range': f'Day 1-{rome_days}', 'place': 'Rome'})
        current_day += rome_days
        # Fly to Riga
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Rome', 'to': 'Riga'})
        current_day += 1
        # Riga stay
        itinerary.append({'day_range': f'Day {current_day}-{current_day + riga_duration - 1}', 'place': 'Riga'})
        current_day += riga_duration

        # Brussels fixed stay
        brussels_start, brussels_duration, brussels_end = self.fixed_stays['Brussels']
        # Fly to Brussels
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': 'Riga', 'to': 'Brussels'})
        current_day += 1
        # Brussels stay
        itinerary.append({'day_range': f'Day {current_day}-{current_day + brussels_duration - 1}', 'place': 'Brussels'})
        current_day += brussels_duration

        # Remaining cities
        remaining = ['Geneva', 'Dubrovnik', 'Valencia']
        for city in remaining:
            duration = self.cities[city]
            itinerary.append({'day_range': f'Day {current_day}-{current_day + duration - 1}', 'place': city})
            current_day += duration
            # Fly to next city
            if remaining.index(city) < len(remaining) - 1:
                next_city = remaining[remaining.index(city) + 1]
                itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': city, 'to': next_city})
                current_day += 1

        # Budapest fixed stay
        budapest_start, budapest_duration, budapest_end = self.fixed_stays['Budapest']
        # Fly to Budapest
        itinerary.append({'flying': f'Day {current_day}-{current_day}', 'from': remaining[-1], 'to': 'Budapest'})
        current_day += 1
        # Budapest stay
        itinerary.append({'day_range': f'Day {current_day}-{current_day + budapest_duration - 1}', 'place': 'Budapest'})

        return itinerary

planner = TripPlanner()
itinerary = planner.compute_itinerary()

# Fix the day ranges and flight days to ensure correct formatting
fixed_itinerary = []
for item in itinerary:
    if 'day_range' in item:
        days = item['day_range'].split('-')
        start = int(days[1])
        end = int(days[2]) if len(days) > 2 else start
        item['day_range'] = f'Day {start}-{end}'
    elif 'flying' in item:
        day = item['flying'].split('-')[1]
        item['flying'] = f'Day {day}'

print(json.dumps(fixed_itinerary, indent=2))