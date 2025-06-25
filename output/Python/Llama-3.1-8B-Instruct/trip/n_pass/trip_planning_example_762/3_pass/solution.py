import json

class TripPlanner:
    def __init__(self, cities, days, constraints):
        self.cities = cities
        self.days = days
        self.constraints = self.validate_constraints(constraints)
        self.itinerary = []

    def validate_constraints(self, constraints):
        validated_constraints = []
        for constraint in constraints:
            if not isinstance(constraint, dict):
                raise ValueError("Constraints must be dictionaries")

            required_keys = ['start_day', 'duration']
            if 'visit' in constraint:
                required_keys.append('visit')
            elif 'visit_relatives' in constraint:
                required_keys.append('visit')
            elif'meet_friends' in constraint:
                required_keys.append('place')
            elif 'attend_wedding' in constraint:
                required_keys.append('place')
            elif 'direct_flight' in constraint:
                required_keys.extend(['direct_flight', 'duration'])

            if not all(key in constraint for key in required_keys):
                raise ValueError(f"Constraint is missing required key: {required_keys}")

            validated_constraints.append(constraint)
        return validated_constraints

    def calculate_itinerary(self):
        # Sort constraints by start day
        constraints = sorted(self.constraints, key=lambda x: x['start_day'])

        # Initialize current city and day
        current_city = 'Dublin'
        current_day = 1

        # Iterate over constraints
        for constraint in constraints:
            # If constraint is to visit a city
            if 'visit' in constraint:
                # Add visit to itinerary
                self.itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + constraint["duration"] - 1}',
                    'place': constraint['visit']
                })

                # Update current city and day
                current_city = constraint['visit']
                current_day += constraint['duration']

            # If constraint is to visit relatives
            elif 'visit_relatives' in constraint:
                # Add visit to relatives to itinerary
                self.itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + constraint["duration"] - 1}',
                    'place': constraint['visit']
                })

                # Update current city and day
                current_city = constraint['visit']
                current_day += constraint['duration']

            # If constraint is to meet friends
            elif'meet_friends' in constraint:
                # Add meeting to itinerary
                self.itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + constraint["duration"] - 1}',
                    'place': constraint['place']
                })

                # Update current city and day
                current_city = constraint['place']
                current_day += constraint['duration']

            # If constraint is to attend a wedding
            elif 'attend_wedding' in constraint:
                # Add wedding to itinerary
                self.itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + constraint["duration"] - 1}',
                    'place': constraint['place']
                })

                # Update current city and day
                current_city = constraint['place']
                current_day += constraint['duration']

            # If constraint is to take a direct flight
            elif 'direct_flight' in constraint:
                # Add flight to itinerary
                self.itinerary.append({
                    'day_range': f'Day {current_day}-{current_day + constraint["duration"] - 1}',
                    'place': f"Flight from {constraint['direct_flight'][0]} to {constraint['direct_flight'][1]}"
                })

                # Update current city and day
                current_city = constraint['direct_flight'][1]
                current_day += constraint['duration']

        # Add remaining days to itinerary
        self.itinerary.append({
            'day_range': f'Day {current_day}-{self.days}',
            'place': current_city
        })

    def output_itinerary(self):
        return {
            'itinerary': self.itinerary
        }

# Define trip constraints
cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
days = 13
constraints = [
    {'visit': 'Dublin', 'duration': 3,'start_day': 1},
    {'visit': 'Madrid', 'duration': 2,'start_day': 4},
    {'visit_relatives': True, 'visit': 'Madrid', 'duration': 2,'start_day': 2},
    {'visit': 'Oslo', 'duration': 3,'start_day': 6},
    {'visit': 'London', 'duration': 2,'start_day': 9},
    {'visit': 'Vilnius', 'duration': 3,'start_day': 11},
    {'visit': 'Berlin', 'duration': 5,'start_day': 12},
    {'attend_wedding': True, 'visit': 'Berlin', 'duration': 5,'start_day': 3},
    {'meet_friends': True, 'place': 'Dublin', 'duration': 2,'start_day': 7},
    {'direct_flight': ['London', 'Madrid'], 'duration': 1},
    {'direct_flight': ['Oslo', 'Vilnius'], 'duration': 1},
    {'direct_flight': ['Berlin', 'Vilnius'], 'duration': 1},
    {'direct_flight': ['Madrid', 'Oslo'], 'duration': 1},
    {'direct_flight': ['Madrid', 'Dublin'], 'duration': 1},
    {'direct_flight': ['London', 'Oslo'], 'duration': 1},
    {'direct_flight': ['Madrid', 'Berlin'], 'duration': 1},
    {'direct_flight': ['Berlin', 'Oslo'], 'duration': 1},
    {'direct_flight': ['Dublin', 'Oslo'], 'duration': 1},
    {'direct_flight': ['London', 'Dublin'], 'duration': 1},
    {'direct_flight': ['London', 'Berlin'], 'duration': 1},
    {'direct_flight': ['Berlin', 'Dublin'], 'duration': 1},
]

# Create trip planner
trip_planner = TripPlanner(cities, days, constraints)

# Calculate itinerary
trip_planner.calculate_itinerary()

# Output itinerary
itinerary = trip_planner.output_itinerary()

# Print itinerary as JSON
print(json.dumps(itinerary, indent=4))