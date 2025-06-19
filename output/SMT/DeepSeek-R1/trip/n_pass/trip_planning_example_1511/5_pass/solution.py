segments = [
    ('A', 1, 7),
    ('B', 9, 9),
    ('C', 12, 12),
    ('D', 14, 14),
    ('E', 17, 17),
    ('F', 19, 19),
    ('G', 21, 21),
    ('A', 24, 24)
]

output = ''.join(f"{city}{start}{end}" for city, start, end in segments)
print(output)