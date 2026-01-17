# Meeting Planning Bucket Structure

This document shows the organization of meeting planning examples by difficulty buckets.

## Bucket Organization

The meeting planning examples are organized into 5 difficulty buckets based on their complexity:

| Bucket | Difficulty Range | Number of Examples | Description |
|--------|------------------|-------------------|-------------|
| 0-20% | 0% - 20% | 20 | Easiest problems - simplest constraint satisfaction |
| 20-40% | 20% - 40% | 20 | Easy problems - straightforward constraints |
| 40-60% | 40% - 60% | 20 | Medium problems - moderate complexity |
| 60-80% | 60% - 80% | 20 | Hard problems - complex constraint interactions |
| 80-100% | 80% - 100% | 20 | Hardest problems - most complex constraint satisfaction |

## Location

The bucket folders are located at:
```
output/Buckets/bucketed_result_groups/meeting/
├── 0-20%/
├── 20-40%/
├── 40-60%/
├── 60-80%/
└── 80-100%/
```

## Example File Format

Each bucket folder contains JSON files with the naming pattern:
- `meeting_planning_example_{ID}_output.json`

The corresponding problem IDs in evaluation results are:
- `meeting_planning_example_{ID}`

## Total Examples

- **Total Examples**: 100
- **Examples per Bucket**: 20
