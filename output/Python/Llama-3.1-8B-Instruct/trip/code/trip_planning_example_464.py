import json
from collections import defaultdict

class TripPlanner:
    def __init__(self):
        self.cities = {
            'Krakow': 5,
            'Frankfurt': 4,
            'Oslo': 3,
            'Dubrovnik': 5,
            'Naples': 5
        }
        self.flights = {
            ('Dubrovnik', 'Oslo'): 1,
            ('Frankfurt', 'Krakow'): 1,
            ('Frankfurt', 'Oslo'): 1,
            ('Dubrovnik', 'Frankfurt'): 1,
            ('Krakow', 'Oslo'): 1,
            ('Naples', 'Oslo'): 1,
            ('Naples', 'Dubrovnik'): 1,
            ('Naples', 'Frankfurt'): 1
        }
        self.meeting = {'Dubrovnik': (5, 9)}
        self.visiting_relatives = {'Oslo': (16, 18)}

    def plan_trip(self):
        trip = []
        days = 0
        current_city = None
        for city, duration in self.cities.items():
            if city in self.meeting:
                start_day, end_day = self.meeting[city]
                trip.append({'day_range': f'Day {start_day}-{end_day}', 'place': city})
                days += end_day - start_day
            elif city in self.visiting_relatives:
                start_day, end_day = self.visiting_relatives[city]
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