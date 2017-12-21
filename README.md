# lrplanarity

```python
>>> import lrplanarity as lrp
>>> K5 = {
...          1 : [2, 3, 4, 5],
...          2 : [1, 3, 4, 5],
...          3 : [1, 2, 4, 5],
...          4 : [1, 2, 3, 5],
...          5 : [1, 2, 3, 4]
...      }
... 
>>> lrp.is_planar(K5)
False
>>> G = {
...         1 : [2, 9, 13],
...         2 : [3, 1, 6],
...         3 : [2, 4, 10],
...         4 : [3, 5, 14],
...         5 : [4, 6, 7, 12, 14],
...         6 : [2, 5],
...         7 : [5, 8, 11],
...         8 : [9, 7, 10],
...         9 : [1, 8, 10],
...         10 : [3, 9, 8],
...         11 : [12, 7, 13],
...         12 : [5, 13, 11],
...         13 : [1, 11, 12],
...         14 : [4, 5]
...     }
... 
>>> lrp.embed(G)
{1: [2, 13, 9], 2: [1, 3, 6], 3: [2, 10, 4], 4: [3, 5, 14], 5: [4, 7, 12, 6, 14], 6: [5, 2], 7: [5, 8, 11], 8: [7, 10, 9], 9: [8, 10, 1], 10: [9, 8, 3], 11: [7, 13, 12], 12: [11, 13, 5], 13: [12, 11, 1], 14: [5, 4]}
```