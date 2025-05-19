import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Oslo': 5,
            'Stuttgart': 5,
            'Reykjavik': 2,
            'Split': 3,
            'Geneva': 2,
            'Porto': 3,
            'Tallinn': 5,
            'Stockholm': 3
        }
        self.flights = {
            ('Reykjavik', 'Stuttgart'): 1,
            ('Reykjavik', 'Stockholm'): 1,
            ('Reykjavik', 'Oslo'): 1,
            ('Stockholm', 'Stuttgart'): 1,
            ('Stockholm', 'Oslo'): 1,
            ('Stuttgart', 'Porto'): 1,
            ('Oslo', 'Split'): 1,
            ('Oslo', 'Geneva'): 1,
            ('Stockholm', 'Split'): 1,
            ('Stockholm', 'Geneva'): 1,
            ('Tallinn', 'Oslo'): 1,
            ('Oslo', 'Porto'): 1,
            ('Geneva', 'Porto'): 1,
            ('Geneva', 'Split'): 1
        }
        self.conference = {'Reykjavik': (1, 2)}
        self.workshop = {'Porto': (19, 21)}
        self.meeting = {'Stockholm': (2, 4)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.conference:
                start_day, end_day = self.conference[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.workshop:
                start_day, end_day = self.workshop[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.meeting:
                start_day, end_day = self.meeting[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            else:
                if current_city is not None:
                    for flight, duration in self.flights.items():
                        if flight[0] == current_city:
                            trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                            days += 1
                trip.append({'day_range': f'Day {days}-{days + duration - 1}', 'place': city})
                days += duration
                current_city = city
        if current_city is not None:
            for flight, duration in self.flights.items():
                if flight[0] == current_city:
                    trip.append({'flying': f'Day {days}-{days}', 'from': current_city, 'to': flight[1]})
                    days += 1
        return trip

    def output_json(self, trip):
        return json.dumps(trip, indent=4)

def main():
    planner = TripPlanner()
    trip = planner.plan_trip()
    print(planner.output_json(trip))

if __name__ == "__main__":
    main()