import heapq

def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

# Read travel times
travel_times = {
    'Financial District': {
        'Golden Gate Park': 23,
        'Chinatown': 5,
        'Union Square': 9,
        'Fisherman's Wharf': 10,
        'Pacific Heights': 13,
        'North Beach': 7,
    },
    'Golden Gate Park': {
        'Financial District': 26,
        'Chinatown': 23,
        'Union Square': 22,
        'Fisherman's Wharf': 24,
        'Pacific Heights': 16,
        'North Beach': 24,
    },
    'Chinatown': {
        'Financial District': 5,
        'Golden Gate Park': 23,
        'Union Square': 7,
        'Fisherman's Wharf': 8,
        'Pacific Heights': 10,
        'North Beach': 3,
    },
    'Union Square': {
        'Financial District': 9,
        'Golden Gate Park': 22,
        'Chinatown': 7,
        'Fisherman's Wharf': 15,
        'Pacific Heights': 15,
        'North Beach': 10,
    },
    'Fisherman's Wharf': {
        'Financial District': 11,
        'Golden Gate Park': 25,
        'Chinatown': 12,
        'Union Square': 13,
        'Pacific Heights': 12,
        'North Beach': 6,
    },
    'Pacific Heights': {
        'Financial District': 13,
        'Golden Gate Park': 15,
        'Chinatown': 11,
        'Union Square': 12,
        'Fisherman's Wharf': 13,
        'North Beach': 9,
    },
    'North Beach': {
        'Financial District': 8,
        'Golden Gate Park': 22,
        'Chinatown': 6,
        'Union Square': 7,
        'Fisherman's Wharf': 5,
        'Pacific Heights': 8,
    }
}

# Read people data and convert times to minutes
people = [
    {
        'name': 'Stephanie',
        'location': 'Golden Gate Park',
        'availability_start': '11:00',
        'availability_end': '15:00',
        'required_time': 105
    },
    {
        'name': 'Karen',
        'location': 'Chinatown',
        'availability_start': '13:45',
        'availability_end': '16:30',
        'required_time': 15
    },
    {
        'name': 'Brian',
        'location': 'Union Square',
        'availability_start': '15:00',
        'availability_end': '17:15',
        'required_time': 30
    },
    {
        'name': 'Rebecca',
        'location': 'Fisherman's Wharf',
        'availability_start': '8:00',
        'availability_end': '11:15',
        'required_time': 30
    },
    {
        'name': 'Joseph',
        'location': 'Pacific Heights',
        'availability_start': '8:15',
        'availability_end': '9:30',
        'required_time': 60
    },
    {
        'name': 'Steven',
        'location': 'North Beach',
        'availability_start': '14:30',
        'availability_end': '20:45',
        'required_time': 120
    }
]

for person in people:
    person['availability_start'] = to_minutes(person['availability_start'])
    person['availability_end'] = to_minutes(person['availability_end'])

# Initialize priority queue
priority_queue = []

for person in people:
    from_loc = 'Financial District'
    to_loc = person['location']
    arrival_time = 540 + travel_times[from_loc][to_loc]
    avail_start = person['availability_start']
    avail_end = person['availability_end']
    required = person['required_time']
    
    earliest_start = max(arrival_time, avail_start)
    latest_start = avail_end - required
    
    if earliest_start <= latest_start:
        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, person))

schedule = []
current_end = 540  # 9:00 AM in minutes

while priority_queue:
    start_min, end_min, person = heapq.heappop(priority_queue)
    
    # Check if this meeting can be scheduled
    if start_min >= current_end:
        # Check if the meeting ends before the person's availability end
        if end_min <= person['availability_end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': format_time(start_min),
                'end_time': format_time(end_min)
            })
            current_end = end_min
            
            # Check for more possible meetings
            for p in people:
                from_loc = 'Financial District'
                to_loc = p['location']
                arrival_time = 540 + travel_times[from_loc][to_loc]
                avail_start = p['availability_start']
                avail_end = p['availability_end']
                required = p['required_time']
                
                earliest_start = max(arrival_time, avail_start)
                latest_start = avail_end - required
                
                if earliest_start <= latest_start:
                    if earliest_start >= current_end:
                        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, p))
    else:
        # This meeting can't be scheduled now, put it back into the queue
        heapq.heappush(priority_queue, (start_min, end_min, person))

# Convert the schedule to the required format
itinerary = []
for meeting in schedule:
    location = meeting['location']
    person = meeting['person']
    start = meeting['start_time']
    end = meeting['end_time']
    itinerary.append({
        'action': 'meet',
        'location': location,
        'person': person,
        'start_time': start,
        'end_time': end
    })

# Convert itinerary to JSON
import json
print(json.dumps({
    "itinerary": itinerary
}))